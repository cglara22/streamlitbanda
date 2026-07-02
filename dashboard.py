"""
BandFlow — Organización de la banda
====================================
Streamlit dashboard adaptado para una banda de música: tareas por miembro
y por área (ensayos, bolos, promo, merch, booking, finanzas, grabación,
logística), con autenticación, Kanban, calendario, agenda y notas.

Basado en TaskFlow (versión IT) — usa su propia base de datos (banda.db).
"""

import calendar
import hashlib
import hmac
import html
import re
import secrets
import sqlite3
import unicodedata
from contextlib import contextmanager
from datetime import date, datetime, timedelta
from pathlib import Path
from typing import Any, Optional

import streamlit as st
import streamlit.components.v1 as components

# ─────────────────────────────────────────────
#  Constants
# ─────────────────────────────────────────────
DB_PATH = Path(__file__).parent / "banda.db"

APP_NAME = "BandFlow"
BAND_NAME = "Los Berlingo"
APP_SUBTITLE = f"{APP_NAME} · Organización de la banda"

STATUS_TODO = "todo"
STATUS_DOING = "doing"
STATUS_DONE = "done"
VALID_STATUSES = (STATUS_TODO, STATUS_DOING, STATUS_DONE)

PRIO_HIGH = "high"
PRIO_MEDIUM = "medium"
PRIO_LOW = "low"
VALID_PRIORITIES = (PRIO_HIGH, PRIO_MEDIUM, PRIO_LOW)

NOTE_STATUS_NOTE = "note"
NOTE_STATUS_PROGRESS = "in_progress"
NOTE_STATUS_RESOLVED = "resolved"
VALID_NOTE_STATUSES = (NOTE_STATUS_NOTE, NOTE_STATUS_PROGRESS, NOTE_STATUS_RESOLVED)

STATUS_LABEL: dict[str, str] = {STATUS_TODO: "To do", STATUS_DOING: "Doing", STATUS_DONE: "Done"}
PRIO_ICON: dict[str, str] = {PRIO_HIGH: "🔴", PRIO_MEDIUM: "🟡", PRIO_LOW: "🟢"}
PRIO_LABEL: dict[str, str] = {PRIO_HIGH: "Alta", PRIO_MEDIUM: "Media", PRIO_LOW: "Baja"}

NOTE_LABEL: dict[str, str] = {
    NOTE_STATUS_NOTE: "Nota",
    NOTE_STATUS_PROGRESS: "En curso",
    NOTE_STATUS_RESOLVED: "Resuelta",
}
NOTE_ICON: dict[str, str] = {
    NOTE_STATUS_NOTE: "📝",
    NOTE_STATUS_PROGRESS: "⏳",
    NOTE_STATUS_RESOLVED: "✅",
}

# Áreas de trabajo de la banda
AREA_DEFAULT = "direccion"
AREAS: dict[str, str] = {
    "direccion": "🧭 Dirección y Planificación",
    "booking": "📞 Booking",
    "rrss": "📣 RRSS / Marketing",
    "diseno": "🎨 Diseño e imagen",
    "foto_video": "📷 Fotografía y vídeo",
    "ensayo": "🎤 Ensayo",
    "bolo": "🎫 Bolo / Concierto",
    "distribucion": "💿 Distribución digital",
    "prensa": "📰 Prensa y comunicación",
    "finanzas": "💶 Finanzas",
    "logistica": "🚐 Logística",
    "tecnico": "🔊 Equipo técnico",
    "composicion": "🎼 Composición",
    "merch": "👕 Merchandising",
}

# Tipos: tarea con flujo de estados, o evento con fecha (bolo, ensayo…)
KIND_TASK = "task"
KIND_EVENT = "event"
KIND_LABEL: dict[str, str] = {KIND_TASK: "📌 Tarea", KIND_EVENT: "📅 Evento"}

DIAS_ES = ["Lunes", "Martes", "Miércoles", "Jueves", "Viernes", "Sábado", "Domingo"]
MESES_ES = [
    "enero", "febrero", "marzo", "abril", "mayo", "junio",
    "julio", "agosto", "septiembre", "octubre", "noviembre", "diciembre",
]

MIN_PASSWORD_LENGTH = 6

BRAND = "#8b5cf6"
BRAND_DARK = "#6d28d9"


# ─────────────────────────────────────────────
#  Helpers
# ─────────────────────────────────────────────
def esc(text: Any) -> str:
    """Escape HTML para prevenir XSS en contenido renderizado con unsafe_allow_html."""
    return html.escape(str(text)) if text else ""


# ─────────────────────────────────────────────
#  DB helpers — SQLite local o Postgres (Supabase) vía st.secrets["DB_URL"]
# ─────────────────────────────────────────────
def _get_db_url() -> Optional[str]:
    try:
        return st.secrets.get("DB_URL")
    except Exception:
        return None


DB_URL = _get_db_url()
USE_PG = bool(DB_URL)

if USE_PG:
    import psycopg2
    import psycopg2.extras


def _pg_translate(sql: str) -> str:
    """Traduce el SQL escrito para SQLite al dialecto de Postgres."""
    sql = sql.replace("?", "%s")
    sql = sql.replace("INTEGER PRIMARY KEY AUTOINCREMENT", "SERIAL PRIMARY KEY")
    sql = sql.replace("datetime('now')", "to_char(now(), 'YYYY-MM-DD HH24:MI:SS')")
    sql = sql.replace("date('now')", "CURRENT_DATE")
    sql = sql.replace("GROUP_CONCAT(DISTINCT u.name)", "STRING_AGG(DISTINCT u.name, ',')")
    if sql.lstrip().upper().startswith("INSERT OR IGNORE"):
        sql = sql.replace("INSERT OR IGNORE", "INSERT", 1).rstrip() + " ON CONFLICT DO NOTHING"
    sql = re.sub(r"ADD COLUMN (?!IF NOT EXISTS)", "ADD COLUMN IF NOT EXISTS ", sql)
    return sql


class _PgConn:
    """Envoltorio que imita la interfaz de sqlite3.Connection sobre psycopg2."""

    def __init__(self, conn) -> None:
        self._c = conn

    def execute(self, sql: str, params=()):
        cur = self._c.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute(_pg_translate(sql), params or None)
        return cur

    def cursor(self) -> "_PgConn":
        return self

    def commit(self) -> None:
        self._c.commit()

    def close(self) -> None:
        self._c.close()


@contextmanager
def get_conn():
    """Conexión a Postgres (Supabase) si hay DB_URL en secrets; si no, SQLite local."""
    if USE_PG:
        conn = psycopg2.connect(DB_URL)
        try:
            yield _PgConn(conn)
        finally:
            conn.close()
    else:
        conn = sqlite3.connect(DB_PATH, check_same_thread=False)
        conn.row_factory = sqlite3.Row
        try:
            yield conn
        finally:
            conn.close()


# ─────────────────────────────────────────────
#  Password hashing
# ─────────────────────────────────────────────
PBKDF2_ITERATIONS = 200_000


def hash_password(password: str) -> str:
    """PBKDF2-HMAC-SHA256. Almacenado como 'pbkdf2$iteraciones$salt$hash'."""
    salt = secrets.token_hex(16)
    h = hashlib.pbkdf2_hmac(
        "sha256", password.encode(), salt.encode(), PBKDF2_ITERATIONS
    ).hex()
    return f"pbkdf2${PBKDF2_ITERATIONS}${salt}${h}"


def verify_password(password: str, stored: str) -> bool:
    """Verifica una contraseña. Acepta el formato pbkdf2 y el legacy 'salt:hash'."""
    try:
        if stored.startswith("pbkdf2$"):
            _, iters, salt, h = stored.split("$", 3)
            calc = hashlib.pbkdf2_hmac(
                "sha256", password.encode(), salt.encode(), int(iters)
            ).hex()
            return hmac.compare_digest(calc, h)
        # Legacy: SHA-256 simple 'salt:hash'
        salt, h = stored.split(":", 1)
        calc = hashlib.sha256((salt + password).encode()).hexdigest()
        return hmac.compare_digest(calc, h)
    except Exception:
        return False


# ─────────────────────────────────────────────
#  Username helpers
# ─────────────────────────────────────────────
def slug_username(name: str) -> str:
    """
    Convierte un nombre completo en un username tipo slug.
    "Christian Gálvez Lara" → "christian.galvez"
    """
    name = (name or "").strip()
    parts = [p for p in re.split(r"\s+", name) if p]

    if len(parts) >= 2:
        base = f"{parts[0]}.{parts[1]}"
    elif parts:
        base = parts[0]
    else:
        base = "usuario"

    base = base.lower()
    base = unicodedata.normalize("NFKD", base).encode("ascii", "ignore").decode("ascii")
    base = re.sub(r"[^a-z0-9.]", "", base)
    base = re.sub(r"\.+", ".", base).strip(".")
    return base or "usuario"


def _sanitize_username(desired: str) -> str:
    """Normaliza y limpia un username candidato."""
    desired = (desired or "").strip().lower()
    desired = unicodedata.normalize("NFKD", desired).encode("ascii", "ignore").decode("ascii")
    desired = re.sub(r"[^a-z0-9.]", "", desired)
    desired = re.sub(r"\.+", ".", desired).strip(".")
    return desired or "usuario"


def ensure_unique_username(conn: sqlite3.Connection, desired: str) -> str:
    """Asegura unicidad del username añadiendo sufijo numérico si es necesario."""
    desired = _sanitize_username(desired)

    row = conn.execute("SELECT 1 FROM users WHERE username = ? LIMIT 1", (desired,)).fetchone()
    if not row:
        return desired

    i = 2
    while True:
        candidate = f"{desired}{i}"
        row = conn.execute(
            "SELECT 1 FROM users WHERE username = ? LIMIT 1", (candidate,)
        ).fetchone()
        if not row:
            return candidate
        i += 1


# ─────────────────────────────────────────────
#  DB init & migrations
# ─────────────────────────────────────────────
def init_db_and_migrate() -> None:
    """Crea tablas, ejecuta migraciones pendientes y rellena usernames faltantes."""
    with get_conn() as conn:
        cur = conn.cursor()

        cur.execute("""
            CREATE TABLE IF NOT EXISTS users (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                name TEXT NOT NULL UNIQUE,
                email TEXT
            )
        """)

        cur.execute("""
            CREATE TABLE IF NOT EXISTS tasks (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                title TEXT NOT NULL,
                description TEXT,
                status TEXT NOT NULL DEFAULT 'todo',
                priority TEXT NOT NULL DEFAULT 'medium',
                due_date TEXT,
                deleted_at TEXT,
                created_at TEXT NOT NULL DEFAULT (datetime('now')),
                updated_at TEXT NOT NULL DEFAULT (datetime('now'))
            )
        """)

        cur.execute("""
            CREATE TABLE IF NOT EXISTS task_assignees (
                task_id INTEGER NOT NULL,
                user_id INTEGER NOT NULL,
                PRIMARY KEY (task_id, user_id),
                FOREIGN KEY (task_id) REFERENCES tasks(id),
                FOREIGN KEY (user_id) REFERENCES users(id)
            )
        """)

        cur.execute("""
            CREATE TABLE IF NOT EXISTS task_notifications (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                task_id INTEGER NOT NULL,
                user_id INTEGER NOT NULL,
                type TEXT NOT NULL,
                sent_at TEXT NOT NULL DEFAULT (datetime('now')),
                UNIQUE(task_id, user_id, type),
                FOREIGN KEY (task_id) REFERENCES tasks(id),
                FOREIGN KEY (user_id) REFERENCES users(id)
            )
        """)

        cur.execute("""
            CREATE TABLE IF NOT EXISTS task_notes (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                task_id INTEGER NOT NULL,
                user_id INTEGER NOT NULL,
                note TEXT NOT NULL,
                created_at TEXT NOT NULL DEFAULT (datetime('now')),
                FOREIGN KEY (task_id) REFERENCES tasks(id),
                FOREIGN KEY (user_id) REFERENCES users(id)
            )
        """)

        # Migraciones incrementales (se ignoran si la columna/índice ya existe)
        migrations = [
            "ALTER TABLE task_notes ADD COLUMN status TEXT NOT NULL DEFAULT 'note'",
            "ALTER TABLE tasks ADD COLUMN estimated_hours REAL",
            "ALTER TABLE tasks ADD COLUMN tags TEXT",
            "ALTER TABLE users ADD COLUMN password_hash TEXT",
            "ALTER TABLE users ADD COLUMN is_admin INTEGER NOT NULL DEFAULT 0",
            "ALTER TABLE tasks ADD COLUMN closed_at TEXT",
            "ALTER TABLE users ADD COLUMN username TEXT",
            "ALTER TABLE tasks ADD COLUMN area TEXT NOT NULL DEFAULT 'direccion'",
            "ALTER TABLE tasks ADD COLUMN kind TEXT NOT NULL DEFAULT 'task'",
        ]
        for migration in migrations:
            try:
                cur.execute(migration)
            except sqlite3.OperationalError:
                pass

        # Remapear áreas antiguas al catálogo nuevo (idempotente)
        for old, new in [("promo", "rrss"), ("grabacion", "composicion"), ("otro", "direccion")]:
            cur.execute("UPDATE tasks SET area = ? WHERE area = ?", (new, old))

        try:
            cur.execute(
                "CREATE UNIQUE INDEX IF NOT EXISTS idx_users_username_uq ON users(username)"
            )
        except sqlite3.OperationalError:
            pass

        conn.commit()

        # Rellenar usernames vacíos
        rows = conn.execute("SELECT id, name, username FROM users").fetchall()
        for r in rows:
            if not r["username"]:
                desired = slug_username(r["name"])
                unique = ensure_unique_username(conn, desired)
                conn.execute("UPDATE users SET username = ? WHERE id = ?", (unique, r["id"]))
        conn.commit()


# ─────────────────────────────────────────────
#  Auth DB functions
# ─────────────────────────────────────────────
def get_user_by_username(username: str) -> Optional[sqlite3.Row]:
    with get_conn() as conn:
        return conn.execute(
            "SELECT * FROM users WHERE username = ?", (username,)
        ).fetchone()


def set_user_password(user_id: int, password: str) -> None:
    h = hash_password(password)
    with get_conn() as conn:
        conn.execute("UPDATE users SET password_hash = ? WHERE id = ?", (h, user_id))
        conn.commit()


def set_user_admin(user_id: int, is_admin: bool) -> None:
    with get_conn() as conn:
        conn.execute(
            "UPDATE users SET is_admin = ? WHERE id = ?", (1 if is_admin else 0, user_id)
        )
        conn.commit()


def login_user(username: str, password: str) -> Optional[sqlite3.Row]:
    """Retorna el usuario si las credenciales son correctas, None en caso contrario."""
    user = get_user_by_username((username or "").strip().lower())
    if not user or not user["password_hash"]:
        return None
    if verify_password(password, user["password_hash"]):
        # Migrar hashes legacy (sha256 simple) a pbkdf2 al iniciar sesión
        if not user["password_hash"].startswith("pbkdf2$"):
            set_user_password(user["id"], password)
        return user
    return None


# ─────────────────────────────────────────────
#  Business DB functions
# ─────────────────────────────────────────────
def fetch_users() -> list[sqlite3.Row]:
    with get_conn() as conn:
        return conn.execute(
            "SELECT id, name, username, email, is_admin FROM users ORDER BY name"
        ).fetchall()


def fetch_tasks(filters: dict) -> list[sqlite3.Row]:
    """Recupera tareas con filtros avanzados: estado, prioridad, asignado, fechas, tags, etc."""
    include_deleted = bool(filters.get("include_deleted"))
    only_done = bool(filters.get("only_done"))

    where: list[str] = []
    params: list[Any] = []

    # Borradas vs activas
    if include_deleted:
        where.append("t.deleted_at IS NOT NULL")
    else:
        where.append("t.deleted_at IS NULL")

    # Solo done
    if only_done and not include_deleted:
        where.append("t.status = 'done'")

    # Filtro de estado (solo activas, no done-only)
    if (
        not only_done
        and not include_deleted
        and filters.get("status")
        and filters["status"] != "all"
    ):
        where.append("t.status = ?")
        params.append(filters["status"])

    # Filtro de prioridad
    if filters.get("priority") and filters["priority"] != "all":
        where.append("t.priority = ?")
        params.append(filters["priority"])

    # Búsqueda de texto
    if q := (filters.get("query") or "").strip():
        where.append("(t.title LIKE ? OR t.description LIKE ? OR t.tags LIKE ?)")
        like = f"%{q}%"
        params.extend([like, like, like])

    date_from = filters.get("date_from")
    date_to = filters.get("date_to")

    # Fechas para tareas activas (por due_date)
    if not include_deleted and not only_done:
        if date_from:
            where.append(
                "t.due_date IS NOT NULL AND t.due_date != '' AND date(t.due_date) >= date(?)"
            )
            params.append(date_from.isoformat())
        if date_to:
            where.append(
                "t.due_date IS NOT NULL AND t.due_date != '' AND date(t.due_date) <= date(?)"
            )
            params.append(date_to.isoformat())

    # Fechas para cerradas (por closed_at)
    if not include_deleted and only_done:
        if date_from:
            where.append("date(COALESCE(t.closed_at, t.updated_at)) >= date(?)")
            params.append(date_from.isoformat())
        if date_to:
            where.append("date(COALESCE(t.closed_at, t.updated_at)) <= date(?)")
            params.append(date_to.isoformat())

    # Filtro por asignado
    join_assignee = ""
    if filters.get("assignee_id") is not None and not include_deleted:
        join_assignee = "JOIN task_assignees ta_f ON ta_f.task_id = t.id AND ta_f.user_id = ?"
        params.insert(0, filters["assignee_id"])

    # Filtro por tag
    if filters.get("tag"):
        where.append("t.tags LIKE ?")
        params.append(f"%{filters['tag']}%")

    # Filtro por área de la banda
    if filters.get("area") and filters["area"] != "all":
        where.append("t.area = ?")
        params.append(filters["area"])

    # Orden
    if only_done and not include_deleted:
        order_clause = """
            ORDER BY
                COALESCE(t.closed_at, t.updated_at) DESC,
                t.updated_at DESC
        """
    else:
        order_clause = """
            ORDER BY
                CASE t.status WHEN 'todo' THEN 1 WHEN 'doing' THEN 2 ELSE 3 END,
                CASE t.priority WHEN 'high' THEN 1 WHEN 'medium' THEN 2 ELSE 3 END,
                COALESCE(t.due_date, '9999-12-31') ASC,
                t.updated_at DESC
        """

    where_clause = " AND ".join(where) if where else "1=1"

    sql = f"""
        SELECT
            t.*,
            GROUP_CONCAT(DISTINCT u.name) AS assignees,
            COALESCE(MAX(nc.notes_count), 0) AS notes_count
        FROM tasks t {join_assignee}
        LEFT JOIN task_assignees ta ON ta.task_id = t.id
        LEFT JOIN users u ON u.id = ta.user_id
        LEFT JOIN (
            SELECT task_id, COUNT(*) AS notes_count
            FROM task_notes
            GROUP BY task_id
        ) nc ON nc.task_id = t.id
        WHERE {where_clause}
        GROUP BY t.id
        {order_clause}
    """

    with get_conn() as conn:
        return conn.execute(sql, params).fetchall()


def get_all_tags() -> list[str]:
    """Retorna la lista de tags únicos ordenados alfabéticamente."""
    with get_conn() as conn:
        rows = conn.execute(
            "SELECT tags FROM tasks WHERE tags IS NOT NULL AND deleted_at IS NULL"
        ).fetchall()

    tags: set[str] = set()
    for r in rows:
        if r["tags"]:
            for t in r["tags"].split(","):
                t = t.strip()
                if t:
                    tags.add(t)
    return sorted(tags)


def add_user(
    name: str,
    email: str,
    password: Optional[str] = None,
    is_admin: bool = False,
    username: Optional[str] = None,
) -> tuple[bool, str]:
    """Crea un usuario. Retorna (ok, username_o_error)."""
    name = (name or "").strip()
    email = (email or "").strip() or None
    if not name:
        return False, "Nombre vacío"

    with get_conn() as conn:
        try:
            desired = username.strip().lower() if username else slug_username(name)
            unique_username = ensure_unique_username(conn, desired)

            conn.execute(
                "INSERT OR IGNORE INTO users(name, email, username) VALUES (?, ?, ?)",
                (name, email, unique_username),
            )
            conn.commit()

            row = conn.execute("SELECT id FROM users WHERE name = ?", (name,)).fetchone()
            if row and password:
                h = hash_password(password)
                conn.execute(
                    "UPDATE users SET password_hash = ?, is_admin = ?, username = ? WHERE id = ?",
                    (h, 1 if is_admin else 0, unique_username, row["id"]),
                )
                conn.commit()

            return True, unique_username
        except Exception as e:
            return False, str(e)


def add_task(
    title: str,
    description: str,
    assignee_ids: list[int],
    priority: str,
    due_date: Optional[str],
    estimated_hours: Optional[float] = None,
    tags: Optional[list[str]] = None,
    area: str = AREA_DEFAULT,
    kind: str = KIND_TASK,
) -> Optional[int]:
    """Crea una tarea o evento. Retorna el task_id o None si falta el título."""
    title = (title or "").strip()
    if not title:
        return None
    if area not in AREAS:
        area = AREA_DEFAULT
    if kind not in (KIND_TASK, KIND_EVENT):
        kind = KIND_TASK

    tags_str = ",".join(t.strip() for t in (tags or []) if t.strip()) or None

    insert_sql = (
        "INSERT INTO tasks"
        "(title, description, status, priority, due_date, deleted_at, "
        " updated_at, estimated_hours, tags, closed_at, area, kind) "
        "VALUES (?, ?, 'todo', ?, ?, NULL, datetime('now'), ?, ?, NULL, ?, ?)"
    )
    insert_params = (
        title, (description or "").strip() or None, priority, due_date,
        estimated_hours, tags_str, area, kind,
    )

    with get_conn() as conn:
        cur = conn.cursor()
        if USE_PG:
            row = cur.execute(insert_sql + " RETURNING id", insert_params).fetchone()
            task_id = row["id"]
        else:
            cur.execute(insert_sql, insert_params)
            task_id = cur.lastrowid
        for uid in assignee_ids:
            cur.execute(
                "INSERT OR IGNORE INTO task_assignees(task_id, user_id) VALUES (?, ?)",
                (task_id, uid),
            )
        conn.commit()
    return task_id


def update_task(
    task_id: int,
    title: str,
    description: str,
    status: str,
    priority: str,
    due_date: Optional[str],
    assignee_ids: list[int],
    estimated_hours: Optional[float] = None,
    tags: Optional[list[str]] = None,
    area: str = AREA_DEFAULT,
    kind: str = KIND_TASK,
) -> None:
    """Actualiza una tarea o evento existente."""
    tags_str = ",".join(t.strip() for t in (tags or []) if t.strip()) or None
    if area not in AREAS:
        area = AREA_DEFAULT
    if kind not in (KIND_TASK, KIND_EVENT):
        kind = KIND_TASK
    if kind == KIND_EVENT:
        # Los eventos no tienen flujo de estados
        status = STATUS_TODO

    with get_conn() as conn:
        cur = conn.cursor()

        # Determinar closed_at según el estado — sin f-string en SQL
        if status == STATUS_DONE:
            cur.execute(
                "UPDATE tasks SET title=?, description=?, status=?, priority=?, due_date=?, "
                "updated_at=datetime('now'), estimated_hours=?, tags=?, area=?, kind=?, "
                "closed_at=COALESCE(closed_at, datetime('now')) "
                "WHERE id=? AND deleted_at IS NULL",
                (
                    (title or "").strip(),
                    (description or "").strip() or None,
                    status,
                    priority,
                    due_date,
                    estimated_hours,
                    tags_str,
                    area,
                    kind,
                    task_id,
                ),
            )
        else:
            cur.execute(
                "UPDATE tasks SET title=?, description=?, status=?, priority=?, due_date=?, "
                "updated_at=datetime('now'), estimated_hours=?, tags=?, area=?, kind=?, closed_at=NULL "
                "WHERE id=? AND deleted_at IS NULL",
                (
                    (title or "").strip(),
                    (description or "").strip() or None,
                    status,
                    priority,
                    due_date,
                    estimated_hours,
                    tags_str,
                    area,
                    kind,
                    task_id,
                ),
            )

        cur.execute("DELETE FROM task_assignees WHERE task_id=?", (task_id,))
        for uid in assignee_ids:
            cur.execute(
                "INSERT OR IGNORE INTO task_assignees(task_id, user_id) VALUES (?, ?)",
                (task_id, uid),
            )
        conn.commit()


def get_task_by_id(task_id: int) -> Optional[sqlite3.Row]:
    with get_conn() as conn:
        return conn.execute("SELECT * FROM tasks WHERE id=?", (task_id,)).fetchone()


def set_task_status(task_id: int, status: str) -> None:
    """Cambia el estado de una tarea (todo, doing, done)."""
    if status not in VALID_STATUSES:
        return

    with get_conn() as conn:
        if status == STATUS_DONE:
            conn.execute(
                "UPDATE tasks SET status=?, closed_at=COALESCE(closed_at, datetime('now')), "
                "updated_at=datetime('now') WHERE id=? AND deleted_at IS NULL",
                (status, task_id),
            )
        else:
            conn.execute(
                "UPDATE tasks SET status=?, closed_at=NULL, updated_at=datetime('now') "
                "WHERE id=? AND deleted_at IS NULL",
                (status, task_id),
            )
        conn.commit()


def logical_delete_task(task_id: int) -> None:
    with get_conn() as conn:
        conn.execute(
            "UPDATE tasks SET deleted_at=datetime('now'), updated_at=datetime('now') "
            "WHERE id=? AND deleted_at IS NULL",
            (task_id,),
        )
        conn.commit()


def restore_task(task_id: int) -> None:
    with get_conn() as conn:
        conn.execute(
            "UPDATE tasks SET deleted_at=NULL, updated_at=datetime('now') "
            "WHERE id=? AND deleted_at IS NOT NULL",
            (task_id,),
        )
        conn.commit()


def get_task_assignees(task_id: int) -> list[sqlite3.Row]:
    with get_conn() as conn:
        return conn.execute(
            "SELECT u.id, u.name, u.email FROM task_assignees ta "
            "JOIN users u ON u.id = ta.user_id "
            "WHERE ta.task_id=? ORDER BY u.name",
            (task_id,),
        ).fetchall()


def fetch_task_notes(task_id: int) -> list[sqlite3.Row]:
    with get_conn() as conn:
        return conn.execute(
            "SELECT n.id, n.note, n.status, n.created_at, u.name AS user_name "
            "FROM task_notes n JOIN users u ON u.id = n.user_id "
            "WHERE n.task_id=? ORDER BY n.created_at DESC",
            (task_id,),
        ).fetchall()


def add_task_note(task_id: int, user_id: int, note: str, status: str = "note") -> None:
    note = (note or "").strip()
    if not note:
        return
    if status not in VALID_NOTE_STATUSES:
        status = NOTE_STATUS_NOTE
    with get_conn() as conn:
        conn.execute(
            "INSERT INTO task_notes(task_id, user_id, note, status) VALUES (?, ?, ?, ?)",
            (task_id, user_id, note, status),
        )
        conn.commit()


def update_task_note_status(note_id: int, status: str) -> None:
    if status not in VALID_NOTE_STATUSES:
        return
    with get_conn() as conn:
        conn.execute("UPDATE task_notes SET status=? WHERE id=?", (status, note_id))
        conn.commit()


def delete_task_note(note_id: int) -> None:
    with get_conn() as conn:
        conn.execute("DELETE FROM task_notes WHERE id=?", (note_id,))
        conn.commit()


def get_stats(
    user_id: Optional[int] = None, only_mine: bool = False
) -> tuple[list[sqlite3.Row], int]:
    """Retorna estadísticas (filas status×priority, nº vencidas)."""
    with get_conn() as conn:
        if only_mine and user_id:
            rows = conn.execute(
                "SELECT t.status, t.priority, COUNT(*) as cnt FROM tasks t "
                "JOIN task_assignees ta ON ta.task_id=t.id AND ta.user_id=? "
                "WHERE t.deleted_at IS NULL GROUP BY t.status, t.priority",
                (user_id,),
            ).fetchall()
            overdue = conn.execute(
                "SELECT COUNT(*) as cnt FROM tasks t "
                "JOIN task_assignees ta ON ta.task_id=t.id AND ta.user_id=? "
                "WHERE t.deleted_at IS NULL AND t.status != 'done' "
                "AND COALESCE(t.kind, 'task') = 'task' "
                "AND t.due_date IS NOT NULL AND date(t.due_date) < date('now')",
                (user_id,),
            ).fetchone()["cnt"]
        else:
            rows = conn.execute(
                "SELECT status, priority, COUNT(*) as cnt "
                "FROM tasks WHERE deleted_at IS NULL GROUP BY status, priority"
            ).fetchall()
            overdue = conn.execute(
                "SELECT COUNT(*) as cnt FROM tasks "
                "WHERE deleted_at IS NULL AND status != 'done' "
                "AND COALESCE(kind, 'task') = 'task' "
                "AND due_date IS NOT NULL AND date(due_date) < date('now')"
            ).fetchone()["cnt"]
    return rows, overdue


# ═════════════════════════════════════════════
#  STREAMLIT APP
# ═════════════════════════════════════════════
st.set_page_config(page_title=f"{BAND_NAME} · {APP_NAME}", layout="wide", page_icon="🎸")

def ensure_bootstrap_admin() -> None:
    """Si la BD está vacía (despliegue nuevo), crea el primer admin desde
    st.secrets (ADMIN_NAME, ADMIN_USER, ADMIN_PASS). Sin secrets no hace nada."""
    with get_conn() as conn:
        n = conn.execute("SELECT COUNT(*) AS c FROM users").fetchone()["c"]
    if n:
        return
    try:
        username = st.secrets.get("ADMIN_USER")
        password = st.secrets.get("ADMIN_PASS")
        name = st.secrets.get("ADMIN_NAME", "Admin")
    except Exception:
        return
    if username and password:
        add_user(name, None, password=password, is_admin=True, username=username)


@st.cache_resource
def _init_once() -> bool:
    """Migraciones y admin inicial: una sola vez por proceso del servidor
    (evita ALTER TABLE y bloqueos en Postgres en cada rerun)."""
    init_db_and_migrate()
    ensure_bootstrap_admin()
    return True


_init_once()

# Session state defaults
_SESSION_DEFAULTS: dict[str, Any] = {
    "logged_in": False,
    "current_user": None,
    "my_view": False,
    "selected_task_id": None,
    "editing_task_id": None,
    "viewing_notes_task_id": None,
    "show_nueva_tarea": False,
    "busy_create_task": False,
    "cal_day": None,
}
for k, v in _SESSION_DEFAULTS.items():
    if k not in st.session_state:
        st.session_state[k] = v


# ─────────────────────────────────────────────
#  Theme-aware CSS
# ─────────────────────────────────────────────
BASE = (st.get_option("theme.base") or "light").lower()
IS_DARK = BASE == "dark"

if IS_DARK:
    SIDEBAR_BG = "#111827"
    SIDEBAR_BORDER = "#1f2937"
    SIDEBAR_TEXT = "#e5e7eb"
    SIDEBAR_MUTED = "#9ca3af"
    INPUT_BG = "#1f2937"
    INPUT_BORDER = "#374151"
    INPUT_TEXT = "#f9fafb"
    PANEL_BG = "#111827"
    # Dark mode extras
    CARD_BG = "#1f2937"
    CARD_BORDER = "#374151"
    CARD_SHADOW = "rgba(0,0,0,.20)"
    METRIC_TEXT = "#f9fafb"
    METRIC_SUB = "#9ca3af"
    METRIC_LABEL = "#9ca3af"
    FORM_BG = "#1f2937"
    FORM_BORDER = "#374151"
    NOTE_BG = "#1f2937"
    NOTE_BORDER = "#374151"
    TEXT_PRIMARY = "#f9fafb"
    TEXT_SECONDARY = "#9ca3af"
else:
    # Sidebar oscura (morado profundo) para contrastar con el contenido claro
    SIDEBAR_BG = "#1e1933"
    SIDEBAR_BORDER = "#2e2749"
    SIDEBAR_TEXT = "#ece9f8"
    SIDEBAR_MUTED = "#a49fc0"
    INPUT_BG = "#2a2447"
    INPUT_BORDER = "#3d3564"
    INPUT_TEXT = "#f4f2fc"
    PANEL_BG = "#f8fafc"
    # Light mode extras
    CARD_BG = "#fafaf8"
    CARD_BORDER = "#e4e2dc"
    CARD_SHADOW = "rgba(0,0,0,.06)"
    METRIC_TEXT = "#111827"
    METRIC_SUB = "#6b7280"
    METRIC_LABEL = "#9ca3af"
    FORM_BG = "#fafaf8"
    FORM_BORDER = "#e4e2dc"
    NOTE_BG = "#fafaf8"
    NOTE_BORDER = "#e4e2dc"
    TEXT_PRIMARY = "#111827"
    TEXT_SECONDARY = "#6b7280"

st.markdown(
    f"""
<style>
/* === FIX: Streamlit 1.50+ icon font === */
@import url('https://fonts.googleapis.com/css2?family=Material+Symbols+Rounded:opsz,wght,FILL,GRAD@20..48,400,0,0');
@import url('https://fonts.googleapis.com/css2?family=Plus+Jakarta+Sans:wght@400;500;600;700;800;900&family=JetBrains+Mono:wght@400;700&display=swap');

span[data-testid="stIconMaterial"],
span[data-testid="stIconMaterial"] span,
[data-testid="stIconMaterial"] {{
  font-family: "Material Symbols Rounded" !important;
  font-variation-settings: "FILL" 0, "wght" 400, "GRAD" 0, "opsz" 24 !important;
  text-transform: none !important; letter-spacing: normal !important;
}}
/* En escritorio la sidebar es fija; en móvil hace falta el control para abrirla */
@media (min-width: 641px) {{
  [data-testid="stSidebarCollapseButton"],
  [data-testid="stSidebarCollapsedControl"] {{ display: none !important }}
}}

/* === GLOBAL RESET === */
*, *::before, *::after {{ box-sizing: border-box }}

/* Menos aire vacío sobre el contenido */
[data-testid="stAppViewContainer"] .block-container {{
  padding-top: 2.2rem !important;
  padding-bottom: 3rem !important;
}}
[data-testid="stHeader"] {{
  background: transparent !important;
  height: 2.4rem !important;
}}
/* Solo la fuente en cascada; el tamaño lo decide cada componente */
html, body, [data-testid="stAppViewContainer"],
[data-testid="stAppViewContainer"] p,
[data-testid="stAppViewContainer"] span,
[data-testid="stAppViewContainer"] div,
[data-testid="stAppViewContainer"] label {{
  font-family: 'Plus Jakarta Sans', sans-serif;
}}
html, body {{ font-size: 15px }}

/* === FADE-IN ANIMATION === */
@keyframes fadeUp {{
  from {{ opacity: 0; transform: translateY(12px); }}
  to   {{ opacity: 1; transform: translateY(0); }}
}}
@keyframes pulse-glow {{
  0%, 100% {{ box-shadow: 0 0 0 0 rgba(139,92,246,.25); }}
  50%      {{ box-shadow: 0 0 0 8px rgba(139,92,246,0); }}
}}
@keyframes shimmer {{
  0%   {{ background-position: -200% 0; }}
  100% {{ background-position: 200% 0; }}
}}
.fade-up {{ animation: fadeUp .4s ease-out both; }}

/* === LOGIN PAGE === */
.login-wrapper {{
  max-width: 400px; margin: 0 auto; padding: 48px 0 0 0;
  animation: fadeUp .5s ease-out both;
}}
.login-logo {{
  text-align: center; margin-bottom: 32px;
}}
.login-logo-icon {{
  display: inline-flex; align-items: center; justify-content: center;
  width: 72px; height: 72px; border-radius: 20px;
  background: linear-gradient(135deg, {BRAND} 0%, {BRAND_DARK} 100%);
  box-shadow: 0 8px 32px rgba(139,92,246,.30);
  font-size: 36px; margin-bottom: 16px;
  animation: pulse-glow 2.5s ease-in-out infinite;
}}
.login-title {{
  font-size: 32px; font-weight: 900; letter-spacing: -.03em;
  color: {TEXT_PRIMARY}; line-height: 1.1;
}}
.login-subtitle {{
  font-size: 15px; color: {TEXT_SECONDARY}; font-weight: 600;
  margin-top: 6px; letter-spacing: .02em;
}}

/* === SIDEBAR === */
[data-testid="stSidebar"] {{
  background: {SIDEBAR_BG} !important;
  border-right: 1px solid {SIDEBAR_BORDER} !important;
}}
[data-testid="stSidebar"] * {{ color: {SIDEBAR_TEXT} !important }}
[data-testid="stSidebar"] label,
[data-testid="stSidebar"] [data-testid="stWidgetLabel"] p {{
  color: {SIDEBAR_MUTED} !important; font-weight: 600 !important;
}}
[data-testid="stSidebar"] .stTextInput input,
[data-testid="stSidebar"] .stSelectbox > div,
[data-testid="stSidebar"] .stMultiSelect > div {{
  background: {INPUT_BG} !important; border: 1px solid {INPUT_BORDER} !important;
  color: {INPUT_TEXT} !important; border-radius: 10px !important; font-size: 14px !important;
  transition: border-color .2s, box-shadow .2s;
}}
[data-testid="stSidebar"] .stTextInput input:focus,
[data-testid="stSidebar"] .stSelectbox > div:focus-within {{
  border-color: {BRAND} !important;
  box-shadow: 0 0 0 3px rgba(139,92,246,.15) !important;
}}
/* Placeholders e icono del ojo legibles sobre la sidebar oscura */
[data-testid="stSidebar"] .stTextInput input::placeholder {{
  color: {SIDEBAR_MUTED} !important; opacity: 1 !important;
}}
[data-testid="stSidebar"] .stTextInput div[data-baseweb="input"],
[data-testid="stSidebar"] .stTextInput div[data-baseweb="base-input"] {{
  background: {INPUT_BG} !important;
  border-color: {INPUT_BORDER} !important;
  border-radius: 10px !important;
}}
[data-testid="stSidebar"] .stTextInput button {{
  background: transparent !important; border: none !important;
}}
[data-testid="stSidebar"] .stTextInput button svg {{
  fill: {SIDEBAR_MUTED} !important; color: {SIDEBAR_MUTED} !important;
}}

/* Streamlit ≥1.5x: los selectbox/date usan estructura BaseWeb distinta */
[data-testid="stSidebar"] div[data-baseweb="select"] > div {{
  background: {INPUT_BG} !important;
  border-color: {INPUT_BORDER} !important;
  color: {INPUT_TEXT} !important;
  border-radius: 10px !important;
}}
[data-testid="stSidebar"] div[data-baseweb="select"] svg {{
  fill: {SIDEBAR_MUTED} !important;
}}
[data-testid="stSidebar"] [data-testid="stDateInput"] div[data-baseweb="input"] {{
  background: {INPUT_BG} !important;
  border-color: {INPUT_BORDER} !important;
  border-radius: 10px !important;
}}
[data-testid="stSidebar"] [data-testid="stDateInput"] input {{
  background: {INPUT_BG} !important;
  color: {INPUT_TEXT} !important;
}}
[data-testid="stSidebar"] [data-testid="stDateInput"] input::placeholder {{
  color: {SIDEBAR_MUTED} !important;
}}
[data-testid="stSidebar"] h1,
[data-testid="stSidebar"] h2,
[data-testid="stSidebar"] h3 {{
  color: {SIDEBAR_MUTED} !important; font-size: 11px !important;
  font-weight: 800 !important; text-transform: uppercase;
  letter-spacing: .10em; margin: 22px 0 8px 0 !important;
}}
[data-testid="stSidebar"] [data-testid="stDivider"] {{
  border-color: {SIDEBAR_BORDER} !important; opacity: .5;
}}

/* === BUTTONS === */
.stButton button {{
  border-radius: 10px !important;
  font-family: 'Plus Jakarta Sans', sans-serif !important;
  font-weight: 700 !important; font-size: 13px !important;
  transition: all .2s cubic-bezier(.4,0,.2,1) !important;
}}
.stButton button:hover {{
  filter: brightness(.93); transform: translateY(-1px);
  box-shadow: 0 4px 12px rgba(0,0,0,.10);
}}
.stButton button:active {{
  transform: translateY(0) scale(.98) !important;
}}

[data-testid="stSidebar"] .stButton button {{
  background: linear-gradient(135deg, {BRAND} 0%, {BRAND_DARK} 100%) !important;
  color: #fff !important; border: none !important;
  font-weight: 800 !important; border-radius: 10px !important;
  width: 100%; font-size: 14px !important;
  box-shadow: 0 2px 8px rgba(139,92,246,.25) !important;
}}

/* USER CHIP */
.user-chip {{
  display: flex; align-items: center; gap: 12px;
  background: linear-gradient(135deg, rgba(139,92,246,.08) 0%, rgba(109,40,217,.04) 100%);
  border: 1px solid rgba(139,92,246,.15);
  border-radius: 14px; padding: 12px 16px; margin-bottom: 6px;
}}
.user-avatar {{
  width: 40px; height: 40px; border-radius: 12px;
  background: linear-gradient(135deg, {BRAND} 0%, {BRAND_DARK} 100%);
  display: flex; align-items: center; justify-content: center;
  font-weight: 900; font-size: 16px; color: #fff; flex-shrink: 0;
  box-shadow: 0 2px 8px rgba(139,92,246,.30);
}}
.user-info-name {{ font-weight: 800; font-size: 14px; color: {SIDEBAR_TEXT} }}
.user-info-role {{ font-size: 12px; color: {SIDEBAR_MUTED}; margin-top: 1px }}

/* MY VIEW TOGGLE */
.myview-btn .stButton button,
[data-testid="stElementContainer"]:has(.myview-btn) + [data-testid="stElementContainer"] .stButton button {{
  background: transparent !important;
  border: 1.5px solid {INPUT_BORDER} !important;
  color: {SIDEBAR_MUTED} !important;
  font-size: 13px !important; border-radius: 10px !important;
  font-weight: 700 !important; text-align: left !important;
  justify-content: flex-start !important; padding: 8px 14px !important;
}}
.myview-btn-active .stButton button,
[data-testid="stElementContainer"]:has(.myview-btn-active) + [data-testid="stElementContainer"] .stButton button {{
  background: linear-gradient(135deg, rgba(139,92,246,.12), rgba(139,92,246,.06)) !important;
  border: 1.5px solid {BRAND} !important;
  color: {BRAND} !important;
}}

/* === TYPOGRAPHY === */
h1 {{
  font-size: 25px !important; font-weight: 900 !important;
  letter-spacing: -.03em; margin-bottom: 0 !important;
  padding-top: 0 !important;
}}
[data-testid="stMarkdownContainer"] p {{ font-size: 15px !important }}
[data-testid="stTextInput"] input, [data-testid="stTextArea"] textarea {{
  font-size: 15px !important; border-radius: 10px !important;
  transition: border-color .2s, box-shadow .2s !important;
}}
[data-testid="stTextInput"] input:focus, [data-testid="stTextArea"] textarea:focus {{
  border-color: {BRAND} !important;
  box-shadow: 0 0 0 3px rgba(139,92,246,.12) !important;
}}
[data-testid="stSelectbox"] span, [data-testid="stMultiSelect"] span {{
  font-size: 15px !important;
}}
[data-testid="stWidgetLabel"] p {{ font-size: 14px !important; font-weight: 600 !important }}

/* === METRICS (theme-aware + icons) === */
.metric-card {{
  background: {CARD_BG}; border-radius: 18px; padding: 18px 20px;
  border: 1px solid {CARD_BORDER};
  box-shadow: 0 1px 3px {CARD_SHADOW}, 0 4px 16px {CARD_SHADOW};
  position: relative; overflow: hidden;
  transition: transform .2s, box-shadow .2s;
}}
.metric-card:hover {{
  transform: translateY(-2px);
  box-shadow: 0 8px 24px {CARD_SHADOW};
}}
.metric-card::before {{
  content: ''; position: absolute; top: 0; left: 0; right: 0; height: 3px;
}}
.mc-total::before {{ background: linear-gradient(90deg, {BRAND}, {BRAND_DARK}) }}
.mc-todo::before  {{ background: linear-gradient(90deg, #f97316, #ea580c) }}
.mc-doing::before {{ background: linear-gradient(90deg, #3b82f6, #2563eb) }}
.mc-done::before  {{ background: linear-gradient(90deg, #22c55e, #16a34a) }}
.mc-overdue::before {{ background: linear-gradient(90deg, #ef4444, #dc2626) }}
.metric-icon {{
  position: absolute; top: 14px; right: 16px;
  font-size: 28px; opacity: .15;
}}
.metric-label {{
  font-size: 12px; color: {METRIC_LABEL}; font-weight: 800;
  text-transform: uppercase; letter-spacing: .08em;
}}
.metric-val {{
  font-size: 30px; font-weight: 900; color: {METRIC_TEXT};
  line-height: 1.1; margin-top: 6px;
  font-feature-settings: "tnum";
}}
.metric-sub {{ font-size: 12px; color: {METRIC_SUB}; margin-top: 4px; font-weight: 600 }}

/* === KANBAN === */
.kanban-col-header {{
  display: flex; align-items: center; gap: 8px;
  padding: 10px 16px; border-radius: 12px;
  margin-bottom: 12px; font-weight: 900; font-size: 15px;
}}
.kh-todo {{
  background: linear-gradient(135deg, #fff7ed, #fef3c7);
  color: #9a3412; border: 1.5px solid #fed7aa;
}}
.kh-doing {{
  background: linear-gradient(135deg, #eff6ff, #dbeafe);
  color: #1e40af; border: 1.5px solid #bfdbfe;
}}
.kh-count {{
  margin-left: auto; background: rgba(0,0,0,.07);
  width: 26px; height: 26px; border-radius: 8px;
  display: flex; align-items: center; justify-content: center;
  font-size: 13px; font-weight: 900;
}}

/* SEGMENTED PILLS (sección, vista y tipo tarea/evento) */
.st-key-seg_seccion [role="radiogroup"],
.st-key-seg_vista [role="radiogroup"],
.st-key-create_kind [role="radiogroup"],
[class*="st-key-edit_kind_"] [role="radiogroup"] {{
  display: inline-flex; gap: 4px;
  background: {PANEL_BG};
  border: 1px solid {CARD_BORDER};
  border-radius: 12px; padding: 4px;
}}
.st-key-seg_seccion label[data-baseweb="radio"],
.st-key-seg_vista label[data-baseweb="radio"],
.st-key-create_kind label[data-baseweb="radio"],
[class*="st-key-edit_kind_"] label[data-baseweb="radio"] {{
  padding: 7px 18px; border-radius: 9px; margin: 0 !important;
  cursor: pointer; transition: background .15s, box-shadow .15s;
}}
.st-key-seg_seccion label[data-baseweb="radio"] > div:first-child,
.st-key-seg_vista label[data-baseweb="radio"] > div:first-child,
.st-key-create_kind label[data-baseweb="radio"] > div:first-child,
[class*="st-key-edit_kind_"] label[data-baseweb="radio"] > div:first-child {{
  display: none;
}}
.st-key-seg_seccion label[data-baseweb="radio"] p,
.st-key-seg_vista label[data-baseweb="radio"] p,
.st-key-create_kind label[data-baseweb="radio"] p,
[class*="st-key-edit_kind_"] label[data-baseweb="radio"] p {{
  font-size: 13px !important; font-weight: 700 !important;
  color: {TEXT_SECONDARY};
}}
.st-key-seg_seccion label[data-baseweb="radio"]:hover p,
.st-key-seg_vista label[data-baseweb="radio"]:hover p,
.st-key-create_kind label[data-baseweb="radio"]:hover p,
[class*="st-key-edit_kind_"] label[data-baseweb="radio"]:hover p {{
  color: {BRAND};
}}
.st-key-seg_seccion label[data-baseweb="radio"]:has(input:checked),
.st-key-seg_vista label[data-baseweb="radio"]:has(input:checked),
.st-key-create_kind label[data-baseweb="radio"]:has(input:checked),
[class*="st-key-edit_kind_"] label[data-baseweb="radio"]:has(input:checked) {{
  background: linear-gradient(135deg, {BRAND}, {BRAND_DARK});
  box-shadow: 0 2px 8px rgba(139,92,246,.35);
}}
.st-key-seg_seccion label[data-baseweb="radio"]:has(input:checked) p,
.st-key-seg_vista label[data-baseweb="radio"]:has(input:checked) p,
.st-key-create_kind label[data-baseweb="radio"]:has(input:checked) p,
[class*="st-key-edit_kind_"] label[data-baseweb="radio"]:has(input:checked) p {{
  color: #fff !important;
}}
@media (max-width: 640px) {{
  .st-key-seg_seccion [role="radiogroup"],
  .st-key-seg_vista [role="radiogroup"] {{ flex-wrap: wrap }}
  .st-key-seg_seccion label[data-baseweb="radio"],
  .st-key-seg_vista label[data-baseweb="radio"] {{ padding: 6px 12px }}
}}

/* CAJÓN DEL TABLERO: filtros + columnas en un mismo recuadro */
.st-key-boardpanel {{
  background: {PANEL_BG};
  border: 1px solid {CARD_BORDER};
  border-radius: 18px;
  padding: 16px !important;
  margin-bottom: 4px;
}}
/* La barra de filtros es una sección del cajón, separada por una línea */
.st-key-filterbar {{
  border-bottom: 1px solid {CARD_BORDER};
  padding-bottom: 12px !important;
  margin-bottom: 10px;
}}
.st-key-filterbar [data-testid="stExpander"] details {{
  border: none !important; background: transparent !important;
}}
.st-key-filterbar [data-testid="stExpander"] summary {{
  font-size: 13px !important; font-weight: 700 !important;
  color: {TEXT_SECONDARY} !important;
}}

/* Panel superior: recoge métricas, progreso y nueva tarea */
.st-key-toppanel {{
  background: {PANEL_BG};
  border: 1px solid {CARD_BORDER};
  border-radius: 18px;
  padding: 16px !important;
  margin-bottom: 4px;
}}
.st-key-toppanel .metric-card {{
  background: {'#ffffff' if not IS_DARK else '#111827'};
}}
.st-key-toppanel .metrics-grid {{ margin-bottom: 4px }}
.st-key-toppanel .progress-wrap {{ margin: 8px 0 12px 0 }}

/* Carriles del Kanban: destacan sobre el cajón del tablero */
[data-testid="stColumn"]:has(.kanban-col-header) {{
  background: {'#ffffff' if not IS_DARK else '#1f2937'};
  border: 1px solid {CARD_BORDER};
  border-radius: 16px;
  padding: 12px !important;
}}

/* === TASK CARDS (theme-aware) === */
.task-card-accent {{
  position: absolute; top: 0; left: 0; bottom: 0; width: 4px;
  border-radius: 4px 0 0 4px;
}}
.accent-todo {{ background: linear-gradient(180deg, #f59e0b, #d97706) }}
.accent-doing {{ background: linear-gradient(180deg, #3b82f6, #2563eb) }}
.accent-done {{ background: linear-gradient(180deg, #22c55e, #16a34a) }}
.accent-event {{ background: linear-gradient(180deg, #8b5cf6, #6d28d9) }}

[data-testid="stVerticalBlockBorderWrapper"] > div,
[data-testid="stVerticalBlock"]:has(> [data-testid="stElementContainer"] .tc-beacon) {{
  position: relative;
  background: {CARD_BG} !important;
  border: 1px solid {CARD_BORDER} !important;
  border-radius: 16px !important;
  box-shadow: 0 1px 3px {CARD_SHADOW}, 0 4px 14px {CARD_SHADOW};
  transition: all .2s cubic-bezier(.4,0,.2,1);
}}
[data-testid="stVerticalBlockBorderWrapper"] > div:hover,
[data-testid="stVerticalBlock"]:has(> [data-testid="stElementContainer"] .tc-beacon):hover {{
  box-shadow: 0 8px 28px rgba(0,0,0,.10) !important;
  transform: translateY(-2px);
}}
/* Tinte por estado (sin JS, vía beacon data-s) */
[data-testid="stVerticalBlock"]:has(> [data-testid="stElementContainer"] .tc-beacon[data-s="todo"])    {{ background: #fff8f0 !important; border-color: #f0d5a0 !important }}
[data-testid="stVerticalBlock"]:has(> [data-testid="stElementContainer"] .tc-beacon[data-s="doing"])   {{ background: #eef3fe !important; border-color: #b8cef7 !important }}
[data-testid="stVerticalBlock"]:has(> [data-testid="stElementContainer"] .tc-beacon[data-s="done"])    {{ background: #edfaf3 !important; border-color: #a5dfc0 !important }}
[data-testid="stVerticalBlock"]:has(> [data-testid="stElementContainer"] .tc-beacon[data-s="deleted"]) {{ background: #f9f9f9 !important; border-color: #e2e2e2 !important }}
[data-testid="stVerticalBlock"]:has(> [data-testid="stElementContainer"] .tc-beacon[data-s="event"])   {{ background: #f7f4ff !important; border-color: #d9caf8 !important }}

/* PRIORITY PILLS */
.prio-pill {{
  display: inline-flex; align-items: center; gap: 4px;
  padding: 2px 9px; border-radius: 999px;
  font-size: 11px; font-weight: 700; letter-spacing: .02em;
  font-family: 'Plus Jakarta Sans', sans-serif;
}}
.prio-high   {{ background: #fef2f2; color: #b91c1c; border: 1px solid #fecaca }}
.prio-medium {{ background: #fffbeb; color: #b45309; border: 1px solid #fde68a }}
.prio-low    {{ background: #f0fdf4; color: #15803d; border: 1px solid #bbf7d0 }}

/* DUE BADGES */
.due-badge {{
  display: inline-flex; align-items: center; gap: 4px;
  padding: 2px 9px; border-radius: 999px;
  font-size: 10.5px; font-weight: 700;
  font-family: 'JetBrains Mono', monospace;
}}
.due-overdue {{ background: #fef2f2; color: #991b1b; border: 1px solid #fecaca }}
.due-today   {{ background: #fffbeb; color: #92400e; border: 1px solid #fde68a; animation: pulse-glow 2s infinite }}
.due-soon    {{ background: #eff6ff; color: #1e40af; border: 1px solid #bfdbfe }}
.due-normal  {{ background: #f3f4f6; color: #374151; border: 1px solid #e5e7eb }}

/* AREA CHIP */
.area-chip {{
  display: inline-flex; align-items: center; gap: 4px;
  padding: 2px 9px; border-radius: 999px;
  font-size: 11px; font-weight: 700; letter-spacing: .02em;
  background: rgba(139,92,246,.10); color: {BRAND_DARK};
  border: 1px solid rgba(139,92,246,.30);
}}

/* EVENT CHIP */
.event-chip {{
  display: inline-flex; align-items: center; gap: 4px;
  padding: 2px 9px; border-radius: 999px;
  font-size: 11px; font-weight: 800; letter-spacing: .02em;
  background: linear-gradient(135deg, {BRAND}, {BRAND_DARK});
  color: #fff;
}}

/* Título de tarjeta con jerarquía clara */
.task-title {{
  font-size: 16px; font-weight: 800; color: {TEXT_PRIMARY};
  line-height: 1.3; margin: 4px 0 2px 0; letter-spacing: -.01em;
}}

/* TAGS */
.tag-chip {{
  display: inline-block; padding: 2px 9px; border-radius: 999px;
  font-size: 11px; font-weight: 700;
  background: linear-gradient(135deg, #f3f4f6, #e5e7eb); color: #374151;
  border: 1px solid {CARD_BORDER}; margin: 2px 2px 2px 0;
}}

/* TASK BUTTONS wrap */
[data-testid="stVerticalBlockBorderWrapper"] .stButton button,
[data-testid="stVerticalBlock"]:has(> [data-testid="stElementContainer"] .tc-beacon) .stButton button {{
  white-space: normal !important; height: auto !important;
  line-height: 1.15 !important; padding: 8px 10px !important;
  text-align: center !important; overflow-wrap: anywhere !important;
  word-break: break-word !important; min-height: 44px !important;
}}
@media (max-width: 1100px) {{
  [data-testid="stVerticalBlockBorderWrapper"] .stButton button,
  [data-testid="stVerticalBlock"]:has(> [data-testid="stElementContainer"] .tc-beacon) .stButton button {{
    font-size: 11px !important; padding: 7px 8px !important;
  }}
}}

/* STATUS BUTTON COLORS (selector viejo + Streamlit ≥1.5x vía hermano adyacente del marcador) */
.btnwrap-todo button[data-testid="baseButton-primary"],
[data-testid="stElementContainer"]:has(.btnwrap-todo) + [data-testid="stElementContainer"] button[data-testid="stBaseButton-primary"]   {{ background: linear-gradient(135deg,#f59e0b,#d97706) !important; color: #fff !important; border: none !important; font-weight: 700 !important; box-shadow: 0 2px 8px rgba(245,158,11,.30) !important }}
.btnwrap-todo button[data-testid="baseButton-secondary"],
[data-testid="stElementContainer"]:has(.btnwrap-todo) + [data-testid="stElementContainer"] button[data-testid="stBaseButton-secondary"] {{ background: #fdf3e3 !important; color: #92541a !important; border: 1px solid #f0d5a0 !important }}
.btnwrap-doing button[data-testid="baseButton-primary"],
[data-testid="stElementContainer"]:has(.btnwrap-doing) + [data-testid="stElementContainer"] button[data-testid="stBaseButton-primary"]   {{ background: linear-gradient(135deg,#3b82f6,#2563eb) !important; color: #fff !important; border: none !important; font-weight: 700 !important; box-shadow: 0 2px 8px rgba(59,130,246,.30) !important }}
.btnwrap-doing button[data-testid="baseButton-secondary"],
[data-testid="stElementContainer"]:has(.btnwrap-doing) + [data-testid="stElementContainer"] button[data-testid="stBaseButton-secondary"] {{ background: #eef3fe !important; color: #2d5cb8 !important; border: 1px solid #b8cef7 !important }}
.btnwrap-done button[data-testid="baseButton-primary"],
[data-testid="stElementContainer"]:has(.btnwrap-done) + [data-testid="stElementContainer"] button[data-testid="stBaseButton-primary"]   {{ background: linear-gradient(135deg,#22c55e,#16a34a) !important; color: #fff !important; border: none !important; font-weight: 700 !important; box-shadow: 0 2px 8px rgba(34,197,94,.30) !important }}
.btnwrap-done button[data-testid="baseButton-secondary"],
[data-testid="stElementContainer"]:has(.btnwrap-done) + [data-testid="stElementContainer"] button[data-testid="stBaseButton-secondary"] {{ background: #edfaf3 !important; color: #1a6b3e !important; border: 1px solid #a5dfc0 !important }}

/* BOTÓN NUEVA TAREA (bloque propio junto a las pills) */
.st-key-toggle_nueva_tarea button {{
  background: linear-gradient(135deg, {BRAND}, {BRAND_DARK}) !important;
  color: #fff !important; border: none !important;
  border-radius: 12px !important; font-weight: 800 !important;
  font-size: 13px !important; padding: 11px 18px !important;
  box-shadow: 0 3px 12px rgba(139,92,246,.35) !important;
}}
.st-key-toggle_nueva_tarea button:hover {{
  filter: brightness(1.08);
  transform: translateY(-1px);
}}
.st-key-toggle_nueva_tarea button:disabled {{
  opacity: .4; box-shadow: none !important;
}}

/* FORMS */
[data-testid="stForm"] {{
  background: {FORM_BG} !important; border: 1px solid {FORM_BORDER} !important;
  border-radius: 18px !important; padding: 24px !important;
  box-shadow: 0 2px 8px {CARD_SHADOW} !important;
}}

/* NOTES */
.note-item {{
  background: {NOTE_BG}; border: 1px solid {NOTE_BORDER};
  border-radius: 14px; padding: 16px 18px; margin-bottom: 12px;
  border-left: 3px solid {BRAND};
  transition: transform .15s;
}}
.note-item:hover {{ transform: translateX(3px) }}
.note-meta {{
  display: flex; align-items: center; flex-wrap: wrap;
  gap: 8px; margin-bottom: 8px;
}}
.note-author {{ font-size: 15px; font-weight: 800; color: {TEXT_PRIMARY} }}
.note-time {{ font-size: 12px; color: {TEXT_SECONDARY}; font-family: 'JetBrains Mono', monospace }}
.note-badge {{
  padding: 3px 10px; border-radius: 999px;
  font-size: 12px; font-weight: 800; margin-left: auto;
}}
.nb-note     {{ background: #f3f4f6; color: #374151 }}
.nb-progress {{ background: #eff6ff; color: #1e40af }}
.nb-resolved {{ background: #f0fdf4; color: #166534 }}
.note-text {{
  font-size: 14px; color: {TEXT_PRIMARY}; line-height: 1.65; margin: 0;
  white-space: pre-wrap;
}}
.note-dot {{
  display: inline-block; width: 10px; height: 10px;
  border-radius: 999px; margin-right: 4px; vertical-align: middle;
}}
.nd-note     {{ background: #9ca3af }}
.nd-progress {{ background: #3b82f6 }}
.nd-resolved {{ background: #22c55e }}

/* CALENDAR (cuadrícula HTML) */
.calx-grid {{
  display: grid; grid-template-columns: repeat(7, 1fr);
  gap: 6px; margin-top: 8px;
}}
.calx-h {{
  text-align: center; font-size: 11px; font-weight: 800;
  text-transform: uppercase; letter-spacing: .10em;
  color: {TEXT_SECONDARY}; padding: 8px 0;
  border-bottom: 2px solid {CARD_BORDER};
}}
.calx-day {{
  min-height: 108px; background: {CARD_BG};
  border: 1px solid {CARD_BORDER}; border-radius: 12px;
  padding: 8px; overflow: hidden;
}}
.calx-day.out  {{ opacity: .40 }}
.calx-day.wend {{ background: {'#eef1f6' if not IS_DARK else '#16202f'} }}
.calx-day.today {{
  border: 2px solid {BRAND};
  box-shadow: 0 0 0 3px rgba(139,92,246,.15);
}}
.calx-num {{
  font-size: 13px; font-weight: 900; color: {TEXT_PRIMARY};
  margin-bottom: 4px;
}}
.calx-day.today .calx-num {{ color: {BRAND} }}
.calx-pill {{
  font-size: 11px; font-weight: 700; line-height: 1.25;
  border-radius: 6px; padding: 3px 6px; margin-top: 4px;
  white-space: nowrap; overflow: hidden; text-overflow: ellipsis;
}}
.px-todo  {{ background: #fff7ed; color: #9a3412; border-left: 3px solid #f59e0b }}
.px-doing {{ background: #eff6ff; color: #1e40af; border-left: 3px solid #3b82f6 }}
.px-done  {{ background: #f0fdf4; color: #166534; border-left: 3px solid #22c55e; opacity: .7 }}
.px-event {{ background: #f3efff; color: #5b21b6; border-left: 3px solid #8b5cf6; font-weight: 800 }}
.calx-more {{
  font-size: 11px; font-weight: 700; color: {TEXT_SECONDARY};
  text-align: center; margin-top: 4px;
}}
.calx-dots {{ display: none; gap: 3px; margin-top: 2px }}
.dotx {{
  display: inline-block; width: 8px; height: 8px; border-radius: 999px;
}}
.dx-todo  {{ background: #f59e0b }}
.dx-doing {{ background: #3b82f6 }}
.dx-done  {{ background: #22c55e }}
.dx-event {{ background: #8b5cf6 }}
.calx-legend {{
  display: flex; gap: 18px; margin-top: 10px;
  font-size: 12px; font-weight: 700; color: {TEXT_SECONDARY};
  align-items: center;
}}
.calx-legend span {{ display: inline-flex; align-items: center; gap: 5px }}

/* Cuadrícula de días clicables (panel contenedor) */
.st-key-calgrid {{
  background: {'#ffffff' if not IS_DARK else '#1f2937'};
  border: 1px solid {CARD_BORDER};
  border-radius: 16px;
  padding: 14px !important;
}}
.st-key-calgrid [data-testid="stHorizontalBlock"] {{
  flex-direction: row !important; flex-wrap: nowrap !important;
  gap: 4px !important; align-items: stretch !important;
  margin-bottom: 6px;
}}
.st-key-calgrid [data-testid="stColumn"] {{
  min-width: 0 !important; flex: 1 1 0 !important; width: auto !important;
}}
.st-key-calgrid .stButton button {{
  padding: 2px 4px !important; min-height: 32px !important;
  font-size: 13px !important; font-weight: 800 !important;
  border-radius: 8px !important;
}}
.st-key-calgrid .stButton button:disabled {{ opacity: .35 }}
.calx-cellbody {{ margin-top: 2px; min-height: 66px }}
.calx-cellbody.out {{ opacity: .45 }}
@media (max-width: 640px) {{
  .calx-grid {{ gap: 3px }}
  .calx-pill, .calx-more {{ display: none }}
  .calx-dots {{ display: flex; flex-wrap: wrap; justify-content: center }}
  .calx-cellbody {{ min-height: 12px }}
  .st-key-calgrid [data-testid="stHorizontalBlock"] {{ gap: 3px !important }}
  .st-key-calgrid .stButton button {{
    min-height: 30px !important; font-size: 11px !important; padding: 0 !important;
  }}
}}

/* AGENDA */
.agenda-section {{
  font-size: 13px; font-weight: 900; text-transform: uppercase;
  letter-spacing: .10em; color: {BRAND};
  margin: 20px 0 4px 0; padding-bottom: 6px;
  border-bottom: 2px solid {CARD_BORDER};
}}
.agenda-section.overdue {{ color: #dc2626 }}
.agenda-head {{
  font-size: 15px; font-weight: 800; color: {TEXT_PRIMARY};
  margin: 14px 0 8px 0;
}}

/* PROGRESS BAR */
.progress-wrap {{
  display: flex; align-items: center; gap: 12px;
  margin: 4px 0 16px 0;
}}
.progress-bar-bg {{
  background: {CARD_BORDER}; border-radius: 999px; height: 8px;
  flex: 1; overflow: hidden;
}}
.progress-bar-fill {{
  height: 8px; border-radius: 999px;
  background: linear-gradient(90deg, {BRAND}, {BRAND_DARK});
  background-size: 200% 100%;
  animation: shimmer 2s ease-in-out infinite;
  transition: width .5s cubic-bezier(.4,0,.2,1);
}}
.progress-pct {{
  font-size: 13px; font-weight: 900; color: {BRAND};
  font-family: 'JetBrains Mono', monospace;
  min-width: 42px; text-align: right;
}}

/* MISC */
hr {{ border-color: {CARD_BORDER} !important }}
.empty-state {{
  text-align: center; padding: 56px 24px; color: {TEXT_SECONDARY};
  background: linear-gradient(180deg, rgba(139,92,246,.03) 0%, transparent 100%);
  border-radius: 20px; border: 2px dashed {CARD_BORDER};
}}
.empty-state-icon {{ font-size: 52px; margin-bottom: 4px }}
.empty-state-text {{ font-size: 16px; font-weight: 700; margin-top: 8px; color: {TEXT_SECONDARY} }}
.empty-state-sub {{
  font-size: 13px; font-weight: 500; margin-top: 4px;
  color: {TEXT_SECONDARY}; opacity: .7;
}}
[data-testid="stAlert"] {{ border-radius: 14px !important; font-size: 15px !important }}

/* DIALOG */
div[data-testid="stDialog"] button[aria-label="Close"],
div[role="dialog"] button[aria-label="Close"] {{ display: none !important }}
div[data-testid="stDialog"] > div:first-child {{
  background: rgba(15,15,25,.55) !important;
  backdrop-filter: blur(6px) !important;
  -webkit-backdrop-filter: blur(6px) !important;
}}
div[role="dialog"] {{
  border-radius: 22px !important;
  box-shadow: 0 24px 64px rgba(0,0,0,.22), 0 4px 16px rgba(0,0,0,.12) !important;
  border: 1px solid {CARD_BORDER} !important;
  overflow: hidden !important;
}}
div[role="dialog"] > div {{ padding: 28px 32px !important }}
div[role="dialog"] [data-testid="stForm"] {{
  background: {FORM_BG} !important;
  border: 1px solid {FORM_BORDER} !important;
  border-radius: 14px !important;
}}

/* === METRICS GRID === */
.metrics-grid {{
  display: grid; grid-template-columns: repeat(5, 1fr);
  gap: 12px; margin-bottom: 12px;
}}

/* === RESPONSIVE / MÓVIL === */
@media (max-width: 768px) {{
  .metric-card {{ padding: 14px 14px }}
  .metric-val  {{ font-size: 28px }}
  h1 {{ font-size: 24px !important }}
}}
@media (max-width: 640px) {{
  h1 {{ font-size: 22px !important }}
  .metrics-grid {{ grid-template-columns: repeat(2, 1fr); gap: 8px }}
  .metric-card {{ padding: 12px 14px; border-radius: 14px }}
  .metric-val  {{ font-size: 24px }}
  .metric-icon {{ font-size: 20px; top: 10px; right: 12px }}

  /* Botones de las tarjetas: mantener 3 en fila (no apilar) */
  [data-testid="stVerticalBlockBorderWrapper"] [data-testid="stHorizontalBlock"],
  [data-testid="stVerticalBlock"]:has(> [data-testid="stElementContainer"] .tc-beacon) [data-testid="stHorizontalBlock"] {{
    flex-direction: row !important; flex-wrap: nowrap !important; gap: 6px !important;
  }}
  [data-testid="stVerticalBlockBorderWrapper"] [data-testid="stHorizontalBlock"] > div,
  [data-testid="stVerticalBlock"]:has(> [data-testid="stElementContainer"] .tc-beacon) [data-testid="stHorizontalBlock"] > div {{
    min-width: 0 !important; flex: 1 1 0 !important; width: auto !important;
  }}
  [data-testid="stVerticalBlockBorderWrapper"] .stButton button,
  [data-testid="stVerticalBlock"]:has(> [data-testid="stElementContainer"] .tc-beacon) .stButton button {{
    font-size: 11px !important; padding: 8px 4px !important; min-height: 42px !important;
  }}

  .kanban-col-header {{ font-size: 15px; padding: 10px 14px }}
  .login-wrapper {{ padding-top: 20px }}
  div[role="dialog"] {{ width: 96vw !important; max-width: 96vw !important }}
  div[role="dialog"] > div {{ padding: 18px 16px !important }}
  [data-testid="stForm"] {{ padding: 16px !important }}
}}
</style>

<script>
(function(){{
  /* BACKDROP BLOCKER: evita que Streamlit cierre el dialog al click en overlay */
  function blockBackdrop(){{
    [
      'div[data-testid="stModal"] > div:first-child',
      'div[data-testid="stDialog"] > div:first-child'
    ].forEach(function(sel){{
      document.querySelectorAll(sel).forEach(function(el){{
        if(el._bb) return;
        el._bb = true;
        el.addEventListener('mousedown',   function(e){{ e.stopPropagation(); e.preventDefault(); }}, true);
        el.addEventListener('click',       function(e){{ e.stopPropagation(); e.preventDefault(); }}, true);
        el.addEventListener('pointerdown', function(e){{ e.stopPropagation(); e.preventDefault(); }}, true);
      }});
    }});
  }}

  /* COLOR BEACON: colorea stVerticalBlockBorderWrapper según data-status */
  var C = {{
    todo:    ['#fff8f0','#f0d5a0'],
    doing:   ['#eef3fe','#b8cef7'],
    done:    ['#edfaf3','#a5dfc0'],
    deleted: ['#f9f9f9','#e2e2e2']
  }};
  function paintCards(){{
    document.querySelectorAll('.tc-beacon[data-s]').forEach(function(b){{
      var c = C[b.dataset.s]; if(!c) return;
      var el = b;
      for(var i=0;i<20;i++){{
        el = el.parentElement; if(!el) break;
        if(el.getAttribute && el.getAttribute('data-testid')==='stVerticalBlockBorderWrapper'){{
          var d = el.querySelector(':scope>div');
          if(d){{
            d.style.setProperty('background',  c[0],'important');
            d.style.setProperty('border-color',c[1],'important');
          }}
          break;
        }}
      }}
    }});
  }}

  function runAll(){{ blockBackdrop(); paintCards(); }}
  var obs = new MutationObserver(function(){{ requestAnimationFrame(runAll); }});
  obs.observe(document.body,{{childList:true,subtree:true}});
  runAll();
  var n=0; var iv=setInterval(function(){{ runAll(); if(++n>=20) clearInterval(iv); }},400);
}})();
</script>
""",
    unsafe_allow_html=True,
)


# ─────────────────────────────────────────────
#  LOGIN
# ─────────────────────────────────────────────
def show_login() -> None:
    _, col, _ = st.columns([1, 1.2, 1])
    with col:
        st.markdown(
            f"""
            <div class="login-wrapper">
              <div class="login-logo">
                <div class="login-logo-icon">🎸</div>
                <div class="login-title">{BAND_NAME}</div>
                <div class="login-subtitle">{APP_SUBTITLE}</div>
              </div>
            </div>
            """,
            unsafe_allow_html=True,
        )

        with st.form("login_form"):
            username = st.text_input(
                "Usuario", placeholder="nombre.apellido (ej. christian.galvez)"
            )
            password = st.text_input("Contraseña", type="password", placeholder="••••••••")
            submitted = st.form_submit_button(
                "Entrar →", type="primary", use_container_width=True
            )

        if submitted:
            user = login_user(username, password)
            if user:
                st.session_state["logged_in"] = True
                st.session_state["current_user"] = dict(user)
                # Todos entran viendo el tablero completo de la banda;
                # "Mi vista" es un filtro opcional para centrarse en lo propio
                st.session_state["my_view"] = False
                st.rerun()
            else:
                st.error("Usuario o contraseña incorrectos.")

        st.markdown(
            f"<div style='text-align:center;margin-top:16px;font-size:13px;"
            f"color:{TEXT_SECONDARY};font-weight:500;'>"
            f"Si no tienes contraseña, pide al administrador que te asigne una."
            f"</div>",
            unsafe_allow_html=True,
        )


if not st.session_state["logged_in"]:
    show_login()
    st.stop()


# ─────────────────────────────────────────────
#  Logged in — shortcuts
# ─────────────────────────────────────────────
CU: dict = st.session_state["current_user"]
IS_ADMIN: bool = bool(CU.get("is_admin"))
MY_VIEW: bool = st.session_state["my_view"]

users = fetch_users()
user_by_name: dict[str, int] = {u["name"]: u["id"] for u in users}
name_by_id: dict[int, str] = {u["id"]: u["name"] for u in users}


# ─────────────────────────────────────────────
#  HTML helpers (con XSS protection)
# ─────────────────────────────────────────────
def due_badge_html(due_date_str: Optional[str]) -> str:
    """Genera HTML del badge de fecha de vencimiento."""
    if not due_date_str:
        return ""
    try:
        d = datetime.strptime(due_date_str, "%Y-%m-%d").date()
    except (ValueError, TypeError):
        return ""
    delta = (d - date.today()).days
    if delta < 0:
        cls, label = "due-overdue", f"⚠️ Vencida {d.strftime('%d/%m')}"
    elif delta == 0:
        cls, label = "due-today", "🔥 Vence hoy"
    elif delta <= 3:
        cls, label = "due-soon", f"📅 {d.strftime('%d/%m')}"
    else:
        cls, label = "due-normal", f"📅 {d.strftime('%d/%m/%Y')}"
    return f'<span class="due-badge {cls}">{label}</span>'


def event_badge_html(due_date_str: Optional[str]) -> str:
    """Badge de fecha para eventos (un evento pasado no está 'vencido')."""
    if not due_date_str:
        return '<span class="due-badge due-normal">📅 Sin fecha</span>'
    try:
        d = datetime.strptime(due_date_str, "%Y-%m-%d").date()
    except (ValueError, TypeError):
        return ""
    delta = (d - date.today()).days
    if delta < 0:
        cls, label = "due-normal", f"✔ Pasado · {d.strftime('%d/%m')}"
    elif delta == 0:
        cls, label = "due-today", "🔥 ¡Hoy!"
    elif delta <= 7:
        cls, label = "due-soon", f"📅 {DIAS_ES[d.weekday()]} {d.day} · en {delta} día{'s' if delta > 1 else ''}"
    else:
        cls, label = "due-normal", f"📅 {d.strftime('%d/%m/%Y')}"
    return f'<span class="due-badge {cls}">{label}</span>'


def tags_html(tags_str: Optional[str]) -> str:
    """Genera HTML de chips de tags (con escape)."""
    if not tags_str:
        return ""
    return " ".join(
        f'<span class="tag-chip">#{esc(t.strip())}</span>'
        for t in tags_str.split(",")
        if t.strip()
    )


# ─────────────────────────────────────────────
#  Sidebar
# ─────────────────────────────────────────────
with st.sidebar:
    initials = "".join(p[0].upper() for p in (CU["name"] or "").split()[:2]) or "U"
    role_label = "👑 Admin" if IS_ADMIN else "🎸 Miembro"

    st.markdown(
        f"""<div class="user-chip">
          <div class="user-avatar">{esc(initials)}</div>
          <div>
            <div class="user-info-name">{esc(CU['name'])}</div>
            <div class="user-info-role">{role_label} · @{esc(CU.get('username', ''))}</div>
          </div>
        </div>""",
        unsafe_allow_html=True,
    )

    mv_cls = "myview-btn-active" if MY_VIEW else "myview-btn"
    st.markdown(f'<div class="{mv_cls}">', unsafe_allow_html=True)
    mv_lbl = "👁 Mi vista  ✓" if MY_VIEW else "👁 Mi vista"
    if st.button(mv_lbl, key="toggle_myview", use_container_width=True):
        st.session_state["my_view"] = not MY_VIEW
        st.rerun()
    st.markdown("</div>", unsafe_allow_html=True)

    if st.button("🚪 Cerrar sesión", key="logout_btn"):
        for k in _SESSION_DEFAULTS:
            st.session_state[k] = _SESSION_DEFAULTS[k]
        st.rerun()

    st.markdown(
        f"""<div style="font-size:16px;font-weight:900;letter-spacing:-.02em;
            padding:4px 0 0 0;
            background:linear-gradient(135deg,{BRAND},{BRAND_DARK});
            -webkit-background-clip:text;-webkit-text-fill-color:transparent;">
            🎸 {BAND_NAME}</div>""",
        unsafe_allow_html=True,
    )

    # --- Admin: gestión de usuarios ---
    if IS_ADMIN:
        st.markdown("### Usuarios")
        new_user_name = st.text_input("Nombre", placeholder="Ej. Marta", key="new_u_name")
        new_user_username = st.text_input(
            "Usuario (opcional)",
            placeholder="marta.sanchez (si lo dejas vacío se autogenera)",
            key="new_u_username",
        )
        new_user_pass = st.text_input(
            "Contraseña",
            type="password",
            placeholder=f"mínimo {MIN_PASSWORD_LENGTH} caracteres",
            key="new_u_pass",
        )
        new_user_admin = st.checkbox("¿Es admin?", key="new_u_admin")

        if st.button("Crear usuario"):
            if not new_user_pass or len(new_user_pass) < MIN_PASSWORD_LENGTH:
                st.warning(
                    f"La contraseña debe tener al menos {MIN_PASSWORD_LENGTH} caracteres."
                )
            else:
                ok, info = add_user(
                    new_user_name,
                    None,
                    password=new_user_pass,
                    is_admin=new_user_admin,
                    username=new_user_username or None,
                )
                if ok:
                    st.toast(f"✅ Usuario creado: @{info}")
                    st.rerun()
                else:
                    st.warning(f"No se pudo crear: {info}")

        st.markdown("### Cambiar contraseña")
        reset_target = st.selectbox(
            "Usuario", [u["name"] for u in users], key="reset_target"
        )
        reset_pass = st.text_input("Nueva contraseña", type="password", key="reset_pass")
        if st.button("Actualizar contraseña"):
            if reset_pass and len(reset_pass) >= MIN_PASSWORD_LENGTH:
                uid = user_by_name[reset_target]
                set_user_password(uid, reset_pass)
                st.toast(f"✅ Contraseña de {reset_target} actualizada")
            else:
                st.warning(f"Mínimo {MIN_PASSWORD_LENGTH} caracteres.")

    # --- Todos: cambiar mi contraseña ---
    st.markdown("### Mi contraseña")
    my_new_pass = st.text_input("Nueva contraseña", type="password", key="my_new_pass")
    if st.button("Cambiar mi contraseña"):
        if my_new_pass and len(my_new_pass) >= MIN_PASSWORD_LENGTH:
            set_user_password(CU["id"], my_new_pass)
            st.toast("✅ Contraseña actualizada")
        else:
            st.warning(f"Mínimo {MIN_PASSWORD_LENGTH} caracteres.")

    # --- Lista del equipo ---
    if users:
        st.markdown("### La banda")
        for u in users:
            ud = dict(u)
            icon = "👑" if ud["is_admin"] else ("📧" if ud["email"] else "👤")
            admin_badge = (
                f'<span style="font-size:10px;font-weight:800;background:rgba(139,92,246,.15);'
                f'color:{BRAND};padding:2px 6px;border-radius:4px;margin-left:4px;">ADMIN</span>'
                if ud["is_admin"] else ""
            )
            st.markdown(
                f"<div style='font-size:14px;padding:5px 0;color:{SIDEBAR_TEXT};'>"
                f"{icon} <b>{esc(ud['name'])}</b>{admin_badge}"
                f"<div style='font-size:12px;color:{SIDEBAR_MUTED};margin-top:1px;padding-left:22px;'>"
                f"@{esc(ud.get('username', ''))}</div></div>",
                unsafe_allow_html=True,
            )


# ─────────────────────────────────────────────
#  Cabecera + selectores + barra de filtros
# ─────────────────────────────────────────────
# Placeholder de cabecera: se rellena tras conocer la sección activa
header_ph = st.container()

# Segmented pills: sección y vista + botón de nueva tarea
seg1, seg2, seg3 = st.columns([1.1, 1.1, 0.6])
with seg1:
    main_view = st.radio(
        "Sección",
        ["Activas", "Cerradas", "Borradas"],
        horizontal=True,
        key="seg_seccion",
        label_visibility="collapsed",
    )
with seg2:
    view_mode = st.radio(
        "Vista",
        ["Kanban", "Calendario", "Agenda"],
        horizontal=True,
        key="seg_vista",
        label_visibility="collapsed",
        disabled=(main_view != "Activas"),
    )
with seg3:
    if st.button(
        "＋ Nueva tarea",
        key="toggle_nueva_tarea",
        use_container_width=True,
        disabled=(main_view != "Activas"),
    ):
        st.session_state["show_nueva_tarea"] = True
        st.rerun()

# Placeholder del panel de métricas (se rellena tras aplicar los filtros)
metrics_ph = st.container()

# Cajón del tablero: barra de filtros + contenido (kanban/calendario/agenda)
board_panel = st.container(key="boardpanel")
with board_panel, st.container(key="filterbar"):
    fb1, fb2, fb3, fb4 = st.columns([2, 1, 1, 1])
    q = fb1.text_input("🔍 Buscar", "", placeholder="Título, descripción, tag…")
    status_filter = fb2.selectbox(
        "Estado",
        ["all", STATUS_TODO, STATUS_DOING, STATUS_DONE],
        format_func=lambda x: "Todos" if x == "all" else STATUS_LABEL.get(x, x),
        disabled=(main_view != "Activas"),
    )
    priority_filter = fb3.selectbox(
        "Prioridad",
        ["all", PRIO_HIGH, PRIO_MEDIUM, PRIO_LOW],
        format_func=lambda x: (
            "Todas" if x == "all" else f"{PRIO_ICON.get(x, '')} {PRIO_LABEL.get(x, x)}"
        ),
        disabled=(main_view == "Borradas"),
    )
    area_filter = fb4.selectbox(
        "Área",
        ["all"] + list(AREAS.keys()),
        format_func=lambda x: "Todas" if x == "all" else AREAS[x],
        disabled=(main_view == "Borradas"),
    )

    with st.expander("Más filtros — fecha, asignado y tags"):
        mf1, mf2, mf3, mf4 = st.columns(4)
        date_from = mf1.date_input(
            "Desde", value=None, key="date_from", disabled=(main_view == "Borradas")
        )
        date_to = mf2.date_input(
            "Hasta", value=None, key="date_to", disabled=(main_view == "Borradas")
        )
        if date_from and date_to and date_from > date_to:
            date_from, date_to = date_to, date_from

        # Todos los miembros pueden filtrar por cualquier asignado;
        # con "Mi vista" activa, el filtro queda fijado al propio usuario
        assignee_id: Optional[int] = None
        if not MY_VIEW:
            assignee_name = mf3.selectbox(
                "Asignado a",
                ["(Todos)"] + list(user_by_name.keys()),
                disabled=(main_view == "Borradas"),
            )
            assignee_id = None if assignee_name == "(Todos)" else user_by_name[assignee_name]
        else:
            assignee_id = CU["id"]
            mf3.markdown(
                f"<div style='font-size:13px;color:{TEXT_SECONDARY};padding-top:32px;'>"
                f"Asignado a: <b style='color:{TEXT_PRIMARY}'>{esc(CU['name'])}</b> (Mi vista)</div>",
                unsafe_allow_html=True,
            )

        all_tags = get_all_tags()
        tag_filter: Optional[str] = None
        if all_tags:
            tag_sel = mf4.selectbox(
                "Tag", ["(Todos)"] + all_tags, disabled=(main_view == "Borradas")
            )
            if tag_sel != "(Todos)":
                tag_filter = tag_sel


# ─────────────────────────────────────────────
#  Fetch tasks
# ─────────────────────────────────────────────
effective_assignee_id = CU["id"] if MY_VIEW else assignee_id

filters = {
    "query": q.strip(),
    "status": status_filter,
    "priority": priority_filter,
    "assignee_id": effective_assignee_id,
    "date_from": date_from,
    "date_to": date_to,
    "include_deleted": (main_view == "Borradas"),
    "tag": tag_filter,
    "area": area_filter,
    "only_done": (main_view == "Cerradas"),
}
tasks = fetch_tasks(filters)

def _is_task(t) -> bool:
    """Las métricas y el kanban solo cuentan tareas, no eventos."""
    return (t["kind"] or KIND_TASK) == KIND_TASK


todo_n = sum(1 for t in tasks if _is_task(t) and t["status"] == STATUS_TODO)
doing_n = sum(1 for t in tasks if _is_task(t) and t["status"] == STATUS_DOING)
done_n = sum(1 for t in tasks if _is_task(t) and t["status"] == STATUS_DONE)
_, overdue_global = get_stats(user_id=CU["id"], only_mine=MY_VIEW)


# ─────────────────────────────────────────────
#  Header + Metrics
# ─────────────────────────────────────────────
if main_view == "Activas":
    view_label = f"👁 Mis tareas — {esc(CU['name'])}" if MY_VIEW else f"🎸 {BAND_NAME} — Panel principal"
elif main_view == "Cerradas":
    view_label = "✅ Cerradas"
else:
    view_label = "🗑️ Papelera"

with header_ph:
    st.markdown(f"# {view_label}")
    st.markdown(
        f"<div style='color:{TEXT_SECONDARY};font-size:14px;margin-top:-6px;margin-bottom:10px;"
        f"font-weight:600;letter-spacing:.01em;'>"
        f"📅 Hoy · {DIAS_ES[date.today().weekday()]} {date.today().day} de "
        f"{MESES_ES[date.today().month - 1]} de {date.today().year}</div>",
        unsafe_allow_html=True,
    )

if main_view == "Activas":
    total = sum(1 for t in tasks if _is_task(t))
    done_pct = int((done_n / total * 100) if total > 0 else 0)

    metric_icon = {"mc-total": "📊", "mc-todo": "📋", "mc-doing": "🔄", "mc-done": "✅", "mc-overdue": "⚠️"}
    cards_html = "".join(
        f"""<div class="metric-card {cls}">
          <span class="metric-icon">{metric_icon.get(cls, '')}</span>
          <div class="metric-label">{label}</div>
          <div class="metric-val">{val}</div>
          <div class="metric-sub">{sub}</div></div>"""
        for label, val, cls, sub in [
            ("Total", total, "mc-total", f"{done_pct}% completado"),
            ("Por hacer", todo_n, "mc-todo", "pendientes"),
            ("En curso", doing_n, "mc-doing", "en progreso"),
            ("Hechas", done_n, "mc-done", "completadas"),
            ("Vencidas", overdue_global, "mc-overdue", "requieren atención"),
        ]
    )
    with metrics_ph, st.container(key="toppanel"):
        st.markdown(f'<div class="metrics-grid">{cards_html}</div>', unsafe_allow_html=True)

        if total > 0:
            st.markdown(
                f"""<div class="progress-wrap">
                  <div class="progress-bar-bg">
                    <div class="progress-bar-fill" style="width:{done_pct}%;"></div>
                  </div>
                  <span class="progress-pct">{done_pct}%</span>
                </div>""",
                unsafe_allow_html=True,
            )




# ─────────────────────────────────────────────
#  Notes dialog
# ─────────────────────────────────────────────
def open_notes_dialog(task_id: int) -> None:
    task = get_task_by_id(task_id)
    if not task:
        return
    task = dict(task)

    notes = fetch_task_notes(task_id)
    nc = len(notes)
    nota_s = "notas" if nc != 1 else "nota"
    nc_label = "Sin notas aún" if nc == 0 else f"{nc} {nota_s}"

    hc1, hc2 = st.columns([5, 1])
    with hc1:
        st.markdown(
            f'<div style="font-size:10px;font-weight:800;text-transform:uppercase;'
            f'letter-spacing:.12em;color:{BRAND};margin-bottom:4px;'
            f'background:linear-gradient(90deg,{BRAND},{BRAND_DARK});'
            f'-webkit-background-clip:text;-webkit-text-fill-color:transparent;">'
            f'NOTAS DE TAREA</div>'
            f'<div style="font-size:18px;font-weight:900;color:{TEXT_PRIMARY};line-height:1.3;">'
            f'{esc(task["title"])}</div>'
            f'<div style="font-size:12px;color:{TEXT_SECONDARY};font-weight:600;margin-top:3px;">'
            f'{nc_label}</div>',
            unsafe_allow_html=True,
        )
    with hc2:
        if st.button("✕ Cerrar", key=f"dlg_close_{task_id}", use_container_width=True):
            st.session_state["viewing_notes_task_id"] = None
            st.rerun()
    st.divider()

    if not notes:
        st.info("📭 Sin notas todavía. Añade la primera abajo.")
    else:
        for n in notes:
            n = dict(n)
            ns = n["status"] if n["status"] in NOTE_LABEL else NOTE_STATUS_NOTE
            dc = {
                NOTE_STATUS_NOTE: "nd-note",
                NOTE_STATUS_PROGRESS: "nd-progress",
                NOTE_STATUS_RESOLVED: "nd-resolved",
            }.get(ns, "nd-note")
            bc = {
                NOTE_STATUS_NOTE: "nb-note",
                NOTE_STATUS_PROGRESS: "nb-progress",
                NOTE_STATUS_RESOLVED: "nb-resolved",
            }.get(ns, "nb-note")
            lbl = f"{NOTE_ICON.get(ns, '📝')} {NOTE_LABEL.get(ns, ns)}"
            ts = (n["created_at"] or "")[:16].replace("T", " ")
            st.markdown(
                f"""<div class="note-item">
                  <div class="note-meta">
                    <span class="note-dot {dc}"></span>
                    <span class="note-author">{esc(n['user_name'])}</span>
                    <span class="note-time">{esc(ts)}</span>
                    <span class="note-badge {bc}">{lbl}</span>
                  </div>
                  <p class="note-text">{esc(n['note'])}</p>
                </div>""",
                unsafe_allow_html=True,
            )
            rc = st.columns([3, 1])
            new_ns = rc[0].selectbox(
                "Estado",
                list(VALID_NOTE_STATUSES),
                index=list(VALID_NOTE_STATUSES).index(ns),
                format_func=lambda x: f"{NOTE_ICON[x]} {NOTE_LABEL[x]}",
                key=f"dlg_ns_{n['id']}_{task_id}",
                label_visibility="collapsed",
            )
            if new_ns != ns:
                update_task_note_status(n["id"], new_ns)
                st.rerun()
            if rc[1].button(
                "🗑️ Borrar", key=f"dlg_del_{n['id']}_{task_id}", use_container_width=True
            ):
                delete_task_note(n["id"])
                st.rerun()

    st.divider()
    st.markdown(
        '<div style="font-size:12px;font-weight:800;text-transform:uppercase;'
        'letter-spacing:.08em;color:#374151;margin-bottom:6px;">✏️ Añadir nota</div>',
        unsafe_allow_html=True,
    )
    with st.form(f"dlg_add_note_form_{task_id}", clear_on_submit=True):
        fc = st.columns(2)
        fc[0].markdown(
            f'<div style="font-size:12px;font-weight:700;color:{TEXT_SECONDARY};'
            f'padding-top:8px;">✍️ Escribiendo como '
            f'<b style="color:{TEXT_PRIMARY};">{esc(CU["name"])}</b></div>',
            unsafe_allow_html=True,
        )
        note_kind = fc[1].selectbox(
            "Tipo",
            list(VALID_NOTE_STATUSES),
            format_func=lambda x: f"{NOTE_ICON[x]} {NOTE_LABEL[x]}",
            key=f"dlg_nk_{task_id}",
        )
        note_text = st.text_area(
            "Nota", placeholder="Describe el avance, problema o comentario…", height=90
        )
        if st.form_submit_button(
            "💾 Guardar nota", type="primary", use_container_width=True
        ):
            if note_text.strip():
                # La nota se firma siempre con el usuario que ha iniciado sesión
                add_task_note(task_id, CU["id"], note_text, note_kind)
                st.toast("✅ Nota guardada")
                st.rerun()
            else:
                st.warning("Escribe algo antes de guardar.")


# ─────────────────────────────────────────────
#  Edit modal
# ─────────────────────────────────────────────
def show_edit_modal(task_id: int) -> None:
    task = get_task_by_id(task_id)
    if not task:
        st.session_state["editing_task_id"] = None
        return
    task = dict(task)
    current_assignees = [row["id"] for row in get_task_assignees(task_id)]

    st.markdown(f"### ✏️ Editar — *{esc(task['title'])}*")

    cur_kind = task.get("kind") if task.get("kind") in (KIND_TASK, KIND_EVENT) else KIND_TASK
    new_kind = st.radio(
        "Tipo",
        [KIND_TASK, KIND_EVENT],
        horizontal=True,
        index=0 if cur_kind == KIND_TASK else 1,
        key=f"edit_kind_{task_id}",
        format_func=lambda k: KIND_LABEL[k],
        label_visibility="collapsed",
    )
    is_event = new_kind == KIND_EVENT

    with st.form(f"edit_task_form_{task_id}"):
        e1, e2 = st.columns([3, 1])
        new_title = e1.text_input("Título *", value=task["title"] or "")
        if is_event:
            new_status = STATUS_TODO
            e2.markdown(
                f"<div style='padding-top:34px;font-size:13px;font-weight:700;"
                f"color:{TEXT_SECONDARY};'>📅 Evento</div>",
                unsafe_allow_html=True,
            )
        else:
            new_status = e2.selectbox(
                "Estado",
                list(VALID_STATUSES),
                index=list(VALID_STATUSES).index(task["status"] or STATUS_TODO),
                format_func=lambda x: STATUS_LABEL[x],
            )
        new_desc = st.text_area("Descripción", value=task["description"] or "", height=100)

        cur_area = task.get("area") if task.get("area") in AREAS else AREA_DEFAULT
        due_val = None
        if task["due_date"]:
            try:
                due_val = datetime.strptime(task["due_date"], "%Y-%m-%d").date()
            except (ValueError, TypeError):
                pass

        if is_event:
            f1, f2 = st.columns(2)
            new_area = f1.selectbox(
                "Área",
                list(AREAS.keys()),
                index=list(AREAS.keys()).index(cur_area),
                format_func=lambda x: AREAS[x],
            )
            new_due = f2.date_input("Fecha", value=due_val)
            new_prio = task["priority"] or PRIO_MEDIUM
            new_est = 0.0
        else:
            f1, f2, f3, f4 = st.columns(4)
            new_prio = f1.selectbox(
                "Prioridad",
                list(VALID_PRIORITIES),
                index=list(VALID_PRIORITIES).index(task["priority"] or PRIO_MEDIUM),
                format_func=lambda x: f"{PRIO_ICON.get(x, '')} {PRIO_LABEL.get(x, x)}",
            )
            new_area = f2.selectbox(
                "Área",
                list(AREAS.keys()),
                index=list(AREAS.keys()).index(cur_area),
                format_func=lambda x: AREAS[x],
            )
            new_due = f3.date_input("Vence", value=due_val)
            new_est = f4.number_input(
                "Horas estimadas",
                min_value=0.0,
                step=0.5,
                value=float(task.get("estimated_hours") or 0.0),
            )
        new_assignees = st.multiselect(
            "Asignados",
            options=[u["id"] for u in users],
            default=current_assignees,
            format_func=lambda uid: name_by_id.get(uid, str(uid)),
        )
        new_tags_raw = st.text_input(
            "Tags (separados por coma)",
            value=task.get("tags") or "",
            placeholder="gira2026, urgente",
        )

        cs = st.columns(2)
        saved = cs[0].form_submit_button(
            "💾 Guardar cambios", type="primary", use_container_width=True
        )
        cancel = cs[1].form_submit_button("✕ Cancelar", use_container_width=True)

        if saved:
            due_str = new_due.isoformat() if isinstance(new_due, date) else None
            tags_list = [t.strip() for t in (new_tags_raw or "").split(",") if t.strip()]
            update_task(
                task_id,
                new_title,
                new_desc,
                new_status,
                new_prio,
                due_str,
                new_assignees,
                estimated_hours=new_est if new_est > 0 else None,
                tags=tags_list,
                area=new_area,
                kind=new_kind,
            )
            st.toast("✅ Guardado")
            st.session_state["editing_task_id"] = None
            st.rerun()
        if cancel:
            st.session_state["editing_task_id"] = None
            st.rerun()


# ─────────────────────────────────────────────
#  Task card
# ─────────────────────────────────────────────
def task_card(
    t: dict,
    is_deleted_view: bool = False,
    compact: bool = False,
    read_only: bool = False,
) -> None:
    """Renderiza una tarjeta de tarea completa con acciones."""
    t = dict(t)
    is_event = (t.get("kind") or KIND_TASK) == KIND_EVENT
    status_ = (t["status"] or STATUS_TODO).lower()
    prio_ = (t["priority"] or PRIO_MEDIUM).lower()
    prio_class = {
        PRIO_LOW: "prio-low",
        PRIO_MEDIUM: "prio-medium",
        PRIO_HIGH: "prio-high",
    }.get(prio_, "prio-medium")

    if is_deleted_view:
        beacon_status = "deleted"
    elif is_event:
        beacon_status = "event"
    else:
        beacon_status = status_

    with st.container(border=True):
        # Beacon para JS coloring + accent bar
        st.markdown(
            f'<span class="tc-beacon" data-s="{beacon_status}"></span>'
            f'<div class="task-card-accent accent-{"event" if is_event else status_}"></div>',
            unsafe_allow_html=True,
        )
        area_ = t.get("area") if t.get("area") in AREAS else AREA_DEFAULT
        if is_event:
            st.markdown(
                f'<span class="event-chip">📅 Evento</span> '
                f'<span class="area-chip">{AREAS[area_]}</span>',
                unsafe_allow_html=True,
            )
        else:
            st.markdown(
                f'<span class="prio-pill {prio_class}">'
                f'{PRIO_ICON.get(prio_, "")} {PRIO_LABEL.get(prio_, prio_)}</span> '
                f'<span class="area-chip">{AREAS[area_]}</span>',
                unsafe_allow_html=True,
            )
        st.markdown(f'<div class="task-title">{esc(t["title"])}</div>', unsafe_allow_html=True)

        # Meta info
        meta_parts: list[str] = []
        if t.get("assignees"):
            meta_parts.append(f"👤 {esc(t['assignees'])}")
        if t.get("estimated_hours"):
            meta_parts.append(f"⏱ {t['estimated_hours']}h estimadas")
        if t.get("notes_count"):
            meta_parts.append(
                f"📝 {t['notes_count']} nota{'s' if t['notes_count'] > 1 else ''}"
            )
        if t.get("closed_at"):
            meta_parts.append(f"✅ Cerrada: {esc(t['closed_at'][:10])}")
        if t.get("deleted_at"):
            meta_parts.append(f"🗑 Borrada: {esc(t['deleted_at'][:10])}")

        badge = (
            event_badge_html(t.get("due_date"))
            if is_event
            else due_badge_html(t.get("due_date"))
        )
        st.markdown(
            f"""<div style="display:flex;flex-wrap:wrap;gap:6px;align-items:center;margin:6px 0;">
              {badge}{tags_html(t.get('tags'))}
            </div>
            <div style="font-size:13px;color:{TEXT_SECONDARY};margin-bottom:8px;">
              {" · ".join(meta_parts)}
            </div>""",
            unsafe_allow_html=True,
        )

        # Descripción (truncada)
        if t.get("description") and not compact:
            desc_raw = t["description"]
            desc = desc_raw[:200] + ("…" if len(desc_raw) > 200 else "")
            st.markdown(
                f'<div style="font-size:14px;color:{TEXT_PRIMARY};margin-bottom:10px;'
                f'line-height:1.5;">{esc(desc)}</div>',
                unsafe_allow_html=True,
            )

        # --- Modo solo lectura (cerradas) ---
        if read_only:
            r = st.columns(2)
            notes_active = st.session_state.get("viewing_notes_task_id") == t["id"]
            nc_lbl = (
                f"📝 Notas ({t['notes_count']})" if t.get("notes_count") else "📝 Notas"
            )
            if r[0].button(
                nc_lbl,
                key=f"notes_ro_{t['id']}",
                use_container_width=True,
                type="primary" if notes_active else "secondary",
            ):
                st.session_state["viewing_notes_task_id"] = (
                    None if notes_active else t["id"]
                )
                st.session_state["editing_task_id"] = None
                st.rerun()
            if r[1].button(
                "✏️ Editar", key=f"edit_ro_{t['id']}", use_container_width=True
            ):
                st.session_state["editing_task_id"] = t["id"]
                st.session_state["viewing_notes_task_id"] = None
                st.rerun()
            return

        # --- Modo activo (con botones de estado) ---
        if not is_deleted_view:
            # Los eventos no tienen flujo de estados
            r1 = [] if is_event else st.columns(3)
            r2 = st.columns(3)

            estados = [] if is_event else [
                (STATUS_TODO, "📋 To do", "btnwrap-todo"),
                (STATUS_DOING, "🔄 Doing", "btnwrap-doing"),
                (STATUS_DONE, "✅ Done", "btnwrap-done"),
            ]
            for col_idx, (status_key, status_label, wrap_cls) in enumerate(estados):
                with r1[col_idx]:
                    st.markdown(f'<div class="{wrap_cls}">', unsafe_allow_html=True)
                    if st.button(
                        status_label,
                        key=f"{status_key}_{t['id']}",
                        use_container_width=True,
                        type="primary" if status_ == status_key else "secondary",
                    ):
                        set_task_status(t["id"], status_key)
                        st.rerun()
                    st.markdown("</div>", unsafe_allow_html=True)

            notes_active = st.session_state.get("viewing_notes_task_id") == t["id"]
            nc_lbl = (
                f"📝 Notas ({t['notes_count']})" if t.get("notes_count") else "📝 Notas"
            )

            if r2[0].button(
                nc_lbl,
                key=f"notes_{t['id']}",
                use_container_width=True,
                type="primary" if notes_active else "secondary",
            ):
                st.session_state["viewing_notes_task_id"] = (
                    None if notes_active else t["id"]
                )
                st.session_state["editing_task_id"] = None
                st.rerun()
            if r2[1].button(
                "✏️ Editar", key=f"edit_{t['id']}", use_container_width=True
            ):
                st.session_state["editing_task_id"] = t["id"]
                st.session_state["viewing_notes_task_id"] = None
                st.rerun()
            if r2[2].button(
                "🗑️ Borrar", key=f"del_{t['id']}", use_container_width=True
            ):
                logical_delete_task(t["id"])
                st.toast("🗑️ Tarea movida a papelera")
                st.rerun()
        else:
            # --- Papelera ---
            b = st.columns(2)
            if b[0].button(
                "♻️ Restaurar", key=f"restore_{t['id']}", use_container_width=True
            ):
                restore_task(t["id"])
                st.toast("♻️ Tarea restaurada")
                st.rerun()


# ─────────────────────────────────────────────
#  Calendar view
# ─────────────────────────────────────────────
def open_day_dialog(day_iso: str, tasks_: list) -> None:
    """Contenido del modal con las tareas completas de un día del calendario."""
    try:
        d = date.fromisoformat(day_iso)
    except (ValueError, TypeError):
        st.session_state["cal_day"] = None
        return

    day_tasks = [t for t in tasks_ if (t["due_date"] or "")[:10] == day_iso]
    label = f"{DIAS_ES[d.weekday()]} {d.day} de {MESES_ES[d.month - 1]} de {d.year}"
    n = len(day_tasks)

    hc1, hc2 = st.columns([4, 1])
    with hc1:
        st.markdown(
            f'<div style="font-size:18px;font-weight:900;color:{TEXT_PRIMARY};">📅 {label}</div>'
            f'<div style="font-size:12px;color:{TEXT_SECONDARY};font-weight:600;margin-top:2px;">'
            f'{n} tarea{"s" if n != 1 else ""}</div>',
            unsafe_allow_html=True,
        )
    with hc2:
        if st.button("✕ Cerrar", key="dlg_close_day", use_container_width=True):
            st.session_state["cal_day"] = None
            st.rerun()
    st.divider()

    if not day_tasks:
        st.info("No hay tareas este día.")
    for t in day_tasks:
        task_card(t, compact=True)


def calendar_view(tasks_: list) -> None:
    """Calendario mensual con días clicables que abren un modal con las tareas."""
    today = date.today()
    years = list(range(today.year - 2, today.year + 4))

    hc1, hc2, _ = st.columns([1, 1, 2])
    year = hc1.selectbox(
        "Año", options=years, index=years.index(today.year), key="cal_year"
    )
    month = hc2.selectbox(
        "Mes",
        options=list(range(1, 13)),
        index=today.month - 1,
        format_func=lambda m: MESES_ES[m - 1].capitalize(),
        key="cal_month",
    )

    by_day: dict[date, list] = {}
    no_due: list = []
    for t in tasks_:
        if t["due_date"]:
            try:
                d = datetime.strptime(t["due_date"], "%Y-%m-%d").date()
                by_day.setdefault(d, []).append(t)
            except ValueError:
                no_due.append(t)
        else:
            no_due.append(t)

    prio_rank = {PRIO_HIGH: 1, PRIO_MEDIUM: 2, PRIO_LOW: 3}
    status_rank = {STATUS_TODO: 1, STATUS_DOING: 2, STATUS_DONE: 3}
    for arr in by_day.values():
        arr.sort(
            key=lambda x: (
                prio_rank.get((x["priority"] or PRIO_MEDIUM).lower(), 2),
                status_rank.get((x["status"] or STATUS_TODO).lower(), 1),
            )
        )

    cal = calendar.Calendar(firstweekday=calendar.MONDAY)
    weeks = cal.monthdatescalendar(year, month)

    MAX_SHOW = 3
    head = "".join(
        f'<div class="calx-h">{d}</div>'
        for d in ["Lun", "Mar", "Mié", "Jue", "Vie", "Sáb", "Dom"]
    )
    with st.container(key="calgrid"):
        st.markdown(f'<div class="calx-grid">{head}</div>', unsafe_allow_html=True)
        for w in weeks:
            cols = st.columns(7, gap="small")
            for i, day in enumerate(w):
                in_month = day.month == month
                is_today = day == today
                day_tasks = by_day.get(day, [])

                with cols[i]:
                    if st.button(
                        str(day.day),
                        key=f"calday_{day.isoformat()}",
                        use_container_width=True,
                        type="primary" if is_today else "secondary",
                        disabled=(len(day_tasks) == 0),
                        help=(
                            f"{len(day_tasks)} tarea(s) — pulsa para verlas"
                            if day_tasks else None
                        ),
                    ):
                        st.session_state["cal_day"] = day.isoformat()
                        st.rerun()

                    pills = ""
                    for t in day_tasks[:MAX_SHOW]:
                        stt = (t["status"] or STATUS_TODO).lower()
                        is_ev = (t["kind"] or KIND_TASK) == KIND_EVENT
                        pill_cls = "event" if is_ev else stt
                        area_ = t["area"] if t["area"] in AREAS else AREA_DEFAULT
                        icon = AREAS[area_].split()[0]
                        estado_lbl = "Evento" if is_ev else STATUS_LABEL.get(stt, stt)
                        full = esc(f"{t['title']} · {AREAS[area_]} · {estado_lbl}")
                        pills += (
                            f'<div class="calx-pill px-{pill_cls}" title="{full}">'
                            f"{icon} {esc(t['title'])}</div>"
                        )
                    if len(day_tasks) > MAX_SHOW:
                        pills += (
                            f'<div class="calx-more">+{len(day_tasks) - MAX_SHOW} más</div>'
                        )

                    dots = "".join(
                        '<span class="dotx dx-{}"></span>'.format(
                            "event"
                            if (t["kind"] or KIND_TASK) == KIND_EVENT
                            else (t["status"] or STATUS_TODO).lower()
                        )
                        for t in day_tasks[:4]
                    )
                    dots_html = f'<div class="calx-dots">{dots}</div>' if dots else ""

                    if pills or dots_html:
                        out_cls = " out" if not in_month else ""
                        st.markdown(
                            f'<div class="calx-cellbody{out_cls}">{dots_html}{pills}</div>',
                            unsafe_allow_html=True,
                        )

    st.markdown(
        f'<div class="calx-legend">'
        f'<span><span class="dotx dx-todo"></span> To do</span>'
        f'<span><span class="dotx dx-doing"></span> Doing</span>'
        f'<span><span class="dotx dx-done"></span> Done</span>'
        f'<span><span class="dotx dx-event"></span> Evento</span>'
        f"</div>",
        unsafe_allow_html=True,
    )

    st.caption(
        "💡 Pulsa el número de un día para ver sus tareas al completo. "
        "En el móvil, la vista **Agenda** muestra lo mismo como lista."
    )

    # Modal con las tareas del día seleccionado (no compite con notas/edición)
    if (
        st.session_state.get("cal_day")
        and not st.session_state.get("viewing_notes_task_id")
        and not st.session_state.get("editing_task_id")
        and not st.session_state.get("show_nueva_tarea")
    ):
        day_iso = st.session_state["cal_day"]
        if hasattr(st, "dialog"):

            @st.dialog("📅 Tareas del día", width="large")
            def _day_dlg() -> None:
                open_day_dialog(day_iso, tasks_)

            _day_dlg()
        else:
            with st.container(border=True):
                open_day_dialog(day_iso, tasks_)

    if no_due:
        with st.expander(f"Sin fecha de vencimiento ({len(no_due)})"):
            for t in no_due:
                task_card(t, compact=True)


# ─────────────────────────────────────────────
#  Agenda view (lista por día — ideal en móvil)
# ─────────────────────────────────────────────
def agenda_view(tasks_: list) -> None:
    """Lista cronológica agrupada por día: vencidas, próximas y sin fecha."""
    today = date.today()

    by_day: dict[date, list] = {}
    no_due: list = []
    for t in tasks_:
        if t["due_date"]:
            try:
                d = datetime.strptime(t["due_date"], "%Y-%m-%d").date()
                by_day.setdefault(d, []).append(t)
            except ValueError:
                no_due.append(t)
        else:
            no_due.append(t)

    overdue_days = sorted(d for d in by_day if d < today)
    upcoming_days = sorted(d for d in by_day if d >= today)

    def day_header(d: date, extra: str = "", color: str = "") -> None:
        label = f"{DIAS_ES[d.weekday()]} {d.day} de {MESES_ES[d.month - 1]}"
        if d.year != today.year:
            label += f" de {d.year}"
        st.markdown(
            f'<div class="agenda-head" style="{color}">📅 {label}{extra}</div>',
            unsafe_allow_html=True,
        )

    if not by_day and not no_due:
        st.markdown(
            '<div class="empty-state"><div class="empty-state-icon">🗓️</div>'
            '<div class="empty-state-text">Nada en la agenda con estos filtros</div>'
            '<div class="empty-state-sub">Crea tareas con fecha para verlas aquí</div></div>',
            unsafe_allow_html=True,
        )
        return

    def _overdue_pending(t) -> bool:
        # Un evento pasado no está "vencido"; solo cuentan las tareas sin cerrar
        return (
            (t["status"] or "") != STATUS_DONE
            and (t["kind"] or KIND_TASK) == KIND_TASK
        )

    pending_overdue = [
        d for d in overdue_days if any(_overdue_pending(t) for t in by_day[d])
    ]
    if pending_overdue:
        st.markdown(
            '<div class="agenda-section overdue">⚠️ Vencidas</div>',
            unsafe_allow_html=True,
        )
        for d in pending_overdue:
            day_header(d, color="color:#b91c1c;")
            for t in by_day[d]:
                if _overdue_pending(t):
                    task_card(t, compact=True)

    if upcoming_days:
        st.markdown(
            '<div class="agenda-section">🗓️ Próximas</div>', unsafe_allow_html=True
        )
        for d in upcoming_days:
            extra = ' · <span style="color:#8b5cf6;">HOY</span>' if d == today else ""
            if d == today + timedelta(days=1):
                extra = " · Mañana"
            day_header(d, extra=extra)
            for t in by_day[d]:
                task_card(t, compact=True)

    if no_due:
        st.markdown(
            '<div class="agenda-section">📌 Sin fecha</div>', unsafe_allow_html=True
        )
        for t in no_due:
            task_card(t, compact=True)


# ─────────────────────────────────────────────
#  Nueva tarea (solo Activas)
# ─────────────────────────────────────────────
def show_create_form() -> None:
    """Formulario de nueva tarea o evento, mostrado en ventana modal."""
    kind_new = st.radio(
        "Tipo",
        [KIND_TASK, KIND_EVENT],
        horizontal=True,
        key="create_kind",
        format_func=lambda k: KIND_LABEL[k],
        label_visibility="collapsed",
    )
    is_event = kind_new == KIND_EVENT

    with st.form("create_task_form", clear_on_submit=True):
        r1c1, r1c2 = st.columns([3, 1])
        title_new = r1c1.text_input(
            "Título *",
            placeholder=(
                "Ej. Bolo en Sala Apolo"
                if is_event
                else "Ej. Reservar sala de ensayo para el sábado"
            ),
        )
        if is_event:
            area_new = r1c2.selectbox(
                "Área",
                list(AREAS.keys()),
                index=list(AREAS.keys()).index("bolo"),
                format_func=lambda x: AREAS[x],
            )
            desc_new = st.text_area(
                "Descripción",
                height=80,
                placeholder="Detalles del evento: sitio, hora, backline…",
            )
            r2c1, r2c2 = st.columns(2)
            due_new = r2c1.date_input("Fecha *", value=None)
            tags_new = r2c2.text_input("Tags", placeholder="gira2026")
            prio_new = PRIO_MEDIUM
            est_new = 0.0
        else:
            prio_new = r1c2.selectbox(
                "Prioridad",
                list(VALID_PRIORITIES),
                index=1,
                format_func=lambda x: f"{PRIO_ICON.get(x, '')} {PRIO_LABEL.get(x, x)}",
            )
            desc_new = st.text_area(
                "Descripción", height=80, placeholder="Detalla el contexto de la tarea…"
            )
            r2c1, r2c2, r2c3, r2c4 = st.columns(4)
            area_new = r2c1.selectbox(
                "Área",
                list(AREAS.keys()),
                index=list(AREAS.keys()).index(AREA_DEFAULT),
                format_func=lambda x: AREAS[x],
            )
            due_new = r2c2.date_input("Vence (opcional)", value=None)
            est_new = r2c3.number_input(
                "Horas estimadas", min_value=0.0, step=0.5, value=0.0
            )
            tags_new = r2c4.text_input("Tags", placeholder="gira2026, urgente")

        default_assignees = (
            [CU["id"]] if CU["id"] in [u["id"] for u in users] else []
        )
        assignees_new = st.multiselect(
            "Asignar a" if not is_event else "Quiénes van",
            options=[u["id"] for u in users],
            default=default_assignees,
            format_func=lambda uid: name_by_id.get(uid, str(uid)),
        )

        cbtns = st.columns(2)
        crear = cbtns[0].form_submit_button(
            "🚀 Crear evento" if is_event else "🚀 Crear tarea",
            type="primary",
            use_container_width=True,
            disabled=st.session_state["busy_create_task"],
        )
        cancelar = cbtns[1].form_submit_button("✕ Cancelar", use_container_width=True)
        if cancelar:
            st.session_state["show_nueva_tarea"] = False
            st.rerun()
        if crear:
            st.session_state["busy_create_task"] = True
            due_str = due_new.isoformat() if isinstance(due_new, date) else None
            tags_list = [t.strip() for t in (tags_new or "").split(",") if t.strip()]
            if is_event and not due_str:
                st.session_state["busy_create_task"] = False
                st.warning("⚠️ Un evento necesita fecha.")
            else:
                task_id = add_task(
                    title_new,
                    desc_new,
                    assignees_new,
                    prio_new,
                    due_str,
                    estimated_hours=est_new if est_new > 0 else None,
                    tags=tags_list,
                    area=area_new,
                    kind=kind_new,
                )
                if task_id:
                    st.toast("✅ Evento creado" if is_event else "✅ Tarea creada")
                    st.session_state["busy_create_task"] = False
                    st.session_state["show_nueva_tarea"] = False
                    st.rerun()
                else:
                    st.session_state["busy_create_task"] = False
                    st.warning("⚠️ Pon un título para crear.")


if main_view == "Activas":
    if (
        st.session_state["show_nueva_tarea"]
        and not st.session_state.get("editing_task_id")
        and not st.session_state.get("viewing_notes_task_id")
    ):
        if hasattr(st, "dialog"):

            @st.dialog("➕ Nueva tarea", width="large")
            def _create_dlg() -> None:
                show_create_form()

            _create_dlg()
        else:
            with st.container(border=True):
                show_create_form()
elif main_view == "Borradas":
    st.caption("Estás en la papelera.")
else:
    st.caption("Tareas cerradas (Done).")


# ─────────────────────────────────────────────
#  Edit modal inline
# ─────────────────────────────────────────────
if st.session_state.get("editing_task_id"):
    _edit_tid = st.session_state["editing_task_id"]
    if hasattr(st, "dialog"):

        @st.dialog("✏️ Editar tarea", width="large")
        def _edit_dlg() -> None:
            show_edit_modal(_edit_tid)

        _edit_dlg()
    else:
        with st.container(border=True):
            show_edit_modal(_edit_tid)
        st.divider()


# ─────────────────────────────────────────────
#  Notes modal
# ─────────────────────────────────────────────
if st.session_state.get("viewing_notes_task_id") and not st.session_state.get("editing_task_id"):
    tid = st.session_state["viewing_notes_task_id"]
    if hasattr(st, "dialog"):

        @st.dialog("📝 Notas")
        def _dlg():
            open_notes_dialog(tid)

        _dlg()
    else:
        components.html("<script>window.scrollTo(0,0);</script>", height=0)
        with st.container(border=True):
            open_notes_dialog(tid)
        st.divider()


# ─────────────────────────────────────────────
#  Main render
# ─────────────────────────────────────────────
with board_panel:

    if main_view == "Borradas":
        st.subheader("🗑️ Papelera")
        if not tasks:
            st.markdown(
                '<div class="empty-state"><div class="empty-state-icon">🗑️</div>'
                '<div class="empty-state-text">La papelera está vacía</div>'
                '<div class="empty-state-sub">Las tareas borradas aparecerán aquí</div></div>',
                unsafe_allow_html=True,
            )
        else:
            for t in tasks:
                task_card(t, is_deleted_view=True)

    elif main_view == "Cerradas":
        st.subheader("✅ Cerradas")
        st.caption("Aquí se guardan las tareas en Done.")
        if not tasks:
            st.markdown(
                '<div class="empty-state"><div class="empty-state-icon">✅</div>'
                '<div class="empty-state-text">No hay tareas cerradas con estos filtros</div>'
                '<div class="empty-state-sub">Completa tareas para verlas aquí</div></div>',
                unsafe_allow_html=True,
            )
        else:
            for t in tasks:
                task_card(t, read_only=True)

    else:
        if view_mode == "Calendario":
            calendar_view(tasks)
        elif view_mode == "Agenda":
            agenda_view(tasks)
        else:
            # Franja de próximos eventos (bolos, ensayos…)
            eventos = [t for t in tasks if (t["kind"] or KIND_TASK) == KIND_EVENT]
            if eventos:
                hoy_iso = date.today().isoformat()
                proximos = sorted(
                    [t for t in eventos if not t["due_date"] or t["due_date"] >= hoy_iso],
                    key=lambda t: t["due_date"] or "9999-12-31",
                )
                pasados = [t for t in eventos if t["due_date"] and t["due_date"] < hoy_iso]

                st.markdown(
                    '<div class="agenda-section">📅 Próximos eventos</div>',
                    unsafe_allow_html=True,
                )
                if proximos:
                    ev_cols = st.columns(min(3, len(proximos)), gap="medium")
                    for i, ev in enumerate(proximos[:6]):
                        with ev_cols[i % len(ev_cols)]:
                            task_card(ev, compact=True)
                else:
                    st.caption("No hay eventos próximos — ¡a mover bolos! 🎸")
                if pasados:
                    with st.expander(f"Eventos pasados ({len(pasados)})"):
                        for ev in pasados:
                            task_card(ev, compact=True)
                st.markdown("")

            # Vista Kanban (solo tareas)
            tasks_by_status: dict[str, list] = {STATUS_TODO: [], STATUS_DOING: []}
            for t in tasks:
                if (t["kind"] or KIND_TASK) == KIND_EVENT:
                    continue
                stt = (t["status"] or STATUS_TODO).lower()
                if stt in (STATUS_TODO, STATUS_DOING):
                    tasks_by_status[stt].append(t)

            col_todo, col_doing = st.columns(2, gap="medium")
            for status_key, title, col, hdr_cls in [
                (STATUS_TODO, "📋 To Do", col_todo, "kh-todo"),
                (STATUS_DOING, "🔄 Doing", col_doing, "kh-doing"),
            ]:
                col_tasks = tasks_by_status.get(status_key, [])
                with col:
                    st.markdown(
                        f"""<div class="kanban-col-header {hdr_cls}">
                          {title}<span class="kh-count">{len(col_tasks)}</span></div>""",
                        unsafe_allow_html=True,
                    )
                    if not col_tasks:
                        st.markdown(
                            '<div class="empty-state" style="padding:28px;">'
                            '<div class="empty-state-icon">✨</div>'
                            '<div class="empty-state-text" style="font-size:14px;">'
                            "Sin tareas aquí</div>"
                            '<div class="empty-state-sub">¡Buen trabajo!</div></div>',
                            unsafe_allow_html=True,
                        )
                    else:
                        for t in col_tasks:
                            task_card(t)