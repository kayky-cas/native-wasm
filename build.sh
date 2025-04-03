set -xe

file_name=$1
basename="${file_name%.*}"

cargo r --message-format=short -- com "$file_name" > $basename.asm && 
    nasm -felf64 "$basename.asm" -o "$basename.o" &&
    ld "$basename.o" -o $basename
