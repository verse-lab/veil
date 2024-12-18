#!/bin/bash

BRANCH=main

git clone https://github.com/verse-lab/veil.git .veil.tmp
cd .veil.tmp && git checkout $BRANCH && cd ..
zip -r veil.zip .veil.tmp && docker build --platform=linux/amd64 . && rm -rf veil.zip .veil.tmp

 
