#!/bin/sh

find src/ -name '[^\.]*.agda' \
    | sed -e 's|^src/[/]*|import |' -e 's|/|.|g' -e 's/.agda//' -e '/import Everything/d' \
    | LC_COLLATE='C' sort \
    | tee  Everything.agda \
    >> index.agda
