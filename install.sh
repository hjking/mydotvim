#!/bin/sh

if [ "$PWD" == "$HOME/.vim" ]; then
    echo "We are in $HOME/.vim"
    exit
elif [ -f "$HOME/.vimrc" ]; then
    echo "$HOME/.vimrc FOUND"
    exit
elif [ -f "$HOME/.gvimrc" ]; then
    echo "$HOME/.gvimrc FOUND"
    exit
else
    echo "linking $PWD to $HOME/.vim"
    \ln -s "$PWD" "$HOME/.vim"
    echo "linking $PWD/vimrc to $HOME/.vimrc"
    \ln -s "$PWD/vimrc" "$HOME/.vimrc"
    echo "linking $PWD/gvimrc to $HOME/.gvimrc"
    \ln -s "$PWD/gvimrc" "$HOME/.gvimrc"
    echo "Update submodules"
    git submodule init
    git submodule update
fi
