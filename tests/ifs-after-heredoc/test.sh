#!./src/dash
dash -c '
cat <<EOF
$@
EOF
echo OK
' - abcdefghijklmnopqrstuvwxyz
