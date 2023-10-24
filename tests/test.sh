#!/usr/bin/env bash

# Clean up previous runs:
rm pass/*.{s,result} &>/dev/null
rm fail/*.{s,result} &>/dev/null

# Create empty `.s` files to ensure that if the compiler does
# not produce output, the interpreter will fail
for i in pass/*.gpy; do
    touch "${i%.gpy}.s"
done

for i in fail/*.gpy; do
    touch "${i%.gpy}.s"
done

# pushd .. &>/dev/null

ERROR=0

echo "Building Project..."
cargo clean
if ! cargo build --release &>/dev/null; then
    cargo check --release
    echo "FAILED TO BUILD PROJECT, ABORTING!"
    exit 1
fi

echo "Running compiler..."
for f in pass/*.gpy; do
    if ! cargo run --release "$f" > "${f%.gpy}.s" 2>/dev/null; then
        echo "$f: INCORRECT - Did not compile example"
        ERROR=1
    fi
done

# popd &>/dev/null || (echo "Unexpected failure" && exit 255)
# popd &>/dev/null || (echo "Unexpected failure" && exit 255)

echo
echo "If any of the following is 'INCORRECT' then there is a bug in your compiler's output"
echo

echo "The following test cases should produce no output:"
echo "This test case is prone to false-positives, ensure your code causes this test case to \
     fail for the right reason (exceeding space on the heap)"
for f in fail/*.s; do
    if ./grumpy-assembly-interp "$f" &>/dev/null; then
        echo "$f: INCORRECT - produced output"
        ERROR=1
    else
        echo "$f: success"
    fi
done
echo

echo "The following test cases should produce output:"
for f in pass/*.s; do
    ./grumpy-assembly-interp "$f" > "${f%.s}.result" 2>/dev/null
    if diff "${f%.s}.result" "${f%.s}.expected" &>/dev/null; then
        echo "$f: success"
    elif [ -f "${f%.s}.result" ]; then # Failed, output file exists
        ERROR=1
        if [ -s "${f%.s}.result" ]; then # Failed, output file is wrong
            echo "$f: INCORRECT - Wrong Output"
        else # Failed, output file is empty
            echo "$f: INCORRECT - Output Empty"
        fi
    fi
done

exit $ERROR
