#!/usr/bin/env bash

# Clean up previous runs:
rm pass/*.{result} &>/dev/null
rm fail/*.{result} &>/dev/null

for f in pass/*.gpy; do
    touch "${f%.gpy}.result"
done

ERROR=0

echo "Building Project..."
# cargo clean
if ! cargo build &>/dev/null; then
    cargo check
    echo "FAILED TO BUILD PROJECT, ABORTING!"
    exit 1
fi

echo "Running tests..."

for f in fail/*.gpy; do
    # echo "running $f"
    if cargo run "$f" > "${f%.gpy}.result" 2>/dev/null; then
        echo "$f: INCORRECT - successfully compiled example"
        ERROR=1
    fi
done

for f in pass/*.gpy; do
    # echo "running $f"
    if ! cargo run "$f" > "${f%.gpy}.result" 2>/dev/null; then
        echo "$f: INCORRECT - Did not compile example"
        ERROR=1
    fi
done

echo "The following test cases should succeed:"
for f in pass/*.gpy; do
    if diff "${f%.gpy}.result" "${f%.gpy}.expected" &>/dev/null; then
	echo "$f: passed"
    elif [ -f "${f%.gpy}.result" ]; then
	ERROR=1
	if [ -s "${f%.gpy}.result" ]; then
	    echo "$f: FAILED - Wrong Output"
	else
	    echo "$f: FAILED - Output Empty"
	fi
    else
	ERROR=1
	echo "$f: FAILED - No Output"
    fi
done

exit $ERROR
