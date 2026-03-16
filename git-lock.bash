#!/bin/bash

# Nombre del archivo que contiene la lista de archivos inmutables
LOCK_LIST="locked_files.txt"

# Función de ayuda
show_help() {
    echo "Uso: ./git-lock.sh [comando] [archivo]"
    echo "Comandos:"
    echo "  lock   <archivo>  : Bloquea el archivo (añade a la lista y quita permisos de escritura)"
    echo "  unlock <archivo>  : Desbloquea el archivo (quita de la lista y restaura permisos)"
    echo "  list              : Muestra los archivos actualmente bloqueados"
    echo "  init              : Inicializa el sistema (crea lista y hook de git)"
}

# Verificar argumentos
if [ $# -eq 0 ]; then
    show_help
    exit 1
fi

COMMAND=$1
FILE=$2

# Asegurar que existe el archivo de lista
touch "$LOCK_LIST"

case $COMMAND in
    lock)
        if [ -z "$FILE" ]; then
            # Sin archivo: proteger el propio locked_files.txt
            chmod a-w "$LOCK_LIST"
            echo "🔒 Permisos de escritura eliminados para '$LOCK_LIST'."
            exit 0
        fi
        if [ ! -f "$FILE" ]; then echo "Error: El archivo '$FILE' no existe."; exit 1; fi

        # 1. Añadir a la lista si no está ya
        if ! grep -Fxq "$FILE" "$LOCK_LIST"; then
            echo "$FILE" >> "$LOCK_LIST"
            echo "Añadido '$FILE' a $LOCK_LIST."
        else
            echo "'$FILE' ya estaba en la lista."
        fi

        # 2. Quitar permisos de escritura (Protección local)
        chmod a-w "$FILE"
        echo "🔒 Permisos de escritura eliminados para '$FILE'."
        ;;

    unlock)
        if [ -z "$FILE" ]; then
            # Sin archivo: restaurar escritura en el propio locked_files.txt
            chmod u+w "$LOCK_LIST"
            echo "🔓 Permisos de escritura restaurados para '$LOCK_LIST'."
            exit 0
        fi
        
        # 1. Eliminar de la lista (crea un temporal y lo renombra)
        if grep -Fxq "$FILE" "$LOCK_LIST"; then
            grep -Fv "$FILE" "$LOCK_LIST" > "${LOCK_LIST}.tmp" && mv "${LOCK_LIST}.tmp" "$LOCK_LIST"
            echo "Eliminado '$FILE' de $LOCK_LIST."
        else
            echo "Advertencia: '$FILE' no estaba en la lista de bloqueados."
        fi
        
        # 2. Restaurar permisos de escritura
        if [ -f "$FILE" ]; then
            chmod u+w "$FILE"
            echo "🔓 Permisos de escritura restaurados para '$FILE'."
        fi
        ;;

    list)
        echo "=== Archivos Bloqueados (en $LOCK_LIST) ==="
        if [ -s "$LOCK_LIST" ]; then
            cat "$LOCK_LIST"
        else
            echo "(Ninguno)"
        fi
        ;;

    init)
        # Crear el archivo de lista
        touch "$LOCK_LIST"
        
        # Instalar el hook de Git
        HOOK_DIR=".git/hooks"
        HOOK_FILE="$HOOK_DIR/pre-commit"
        
        if [ ! -d ".git" ]; then
            echo "Error: No estás en la raíz de un repositorio git."
            exit 1
        fi

        echo "Instalando hook en $HOOK_FILE..."
        
        cat > "$HOOK_FILE" << 'EOF'
#!/bin/bash
# Hook pre-commit para prevenir modificación de archivos bloqueados

LOCK_LIST="locked_files.txt"

# Si no hay lista de bloqueo, permitir todo
if [ ! -f "$LOCK_LIST" ]; then
    exit 0
fi

# Obtener archivos que se intentan commitear (staged)
STAGED_FILES=$(git diff --cached --name-only)
ERROR=0

# Leer lista de bloqueados línea por línea
while IFS= read -r LOCKED_FILE; do
    # Si la línea está vacía, saltar
    [ -z "$LOCKED_FILE" ] && continue
    
    # Comprobar si el archivo bloqueado está en los staged files
    if echo "$STAGED_FILES" | grep -Fqx "$LOCKED_FILE"; then
        echo "❌ ERROR: Estás intentando modificar un archivo bloqueado: $LOCKED_FILE"
        echo "   Para editarlo, primero ejecuta: ./git-lock.sh unlock $LOCKED_FILE"
        ERROR=1
    fi
done < "$LOCK_LIST"

if [ $ERROR -eq 1 ]; then
    exit 1
fi

exit 0
EOF
        
        chmod +x "$HOOK_FILE"
        echo "✅ Sistema de bloqueo inicializado correctamente."
        ;;

    *)
        show_help
        exit 1
        ;;
esac
