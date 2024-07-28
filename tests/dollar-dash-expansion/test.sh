#!./src/dash
set -e
echo "0: the options are $-"
set -fo debug
echo "1: the options are $-"
set +o debug -uo nolog
echo "2: the options are $-"
