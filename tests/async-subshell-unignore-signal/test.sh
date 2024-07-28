#!/bin/sh
shell=src/dash

set -e

SubshellWith() {
        parent_pid=$(setsid "$shell" -c "( $1; sleep 99 ) </dev/null >/dev/null 2>&1 & echo \$\$")
        sleep 1
        subshell_pid=$(ps -o pid= -$parent_pid | tail -n 1)
}

trap 'kill -TERM -$parent_pid 2>/dev//null ||:' EXIT # Tear down after a failure.

echo Scenario 0: '"set -i"' makes a subshell un-ignore SIGINT.
SubshellWith 'set -i'
kill -INT $subshell_pid
if ps -p $subshell_pid | grep -q sleep; then
  echo FAIL
fi
kill -TERM -$parent_pid 2>/dev//null ||: # Tear down.

echo Scenario 1: resetting SIGINT handler.
SubshellWith 'trap - INT'
kill -INT -$parent_pid # kill the whole process group since that's the my use case
if ps -p $subshell_pid | grep -q sleep; then
  echo FAIL
fi
kill -TERM -$parent_pid 2>/dev//null ||: # Tear down.

echo Scenario 2: ignoring SIGINT.
SubshellWith 'trap "" INT'
kill -INT $subshell_pid
if ! ps -p $subshell_pid | grep -q sleep; then
  echo FAIL
fi
kill -TERM -$parent_pid 2>/dev//null ||: # Tear down.

echo OK
