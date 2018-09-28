#!/bin/bash

#Install packages if not already installed
if dpkg-query -W -f'${Status}' xsltproc texlive-full git 2>/dev/null | grep -q "not-installed"
then
    echo Installing debian packages
    sudo apt-get install xsltproc texlive-full git
fi

#git clone Beezer mathbook dependency
if ! [ -e mathbook ]
then
    git clone https://github.com/rbeezer/mathbook.git
fi

#Build HTML documents
if [ -e HTMLbuild ]
then
    rm -rf HTMLbuild
fi
mkdir HTMLbuild
cd HTMLbuild
xsltproc --xinclude ../mathbook/xsl/mathbook-html.xsl ../nazgand-book.xml
cd ..

#Build LaTeX documents
if [ -e LaTeXbuild ]
then
    rm -rf LaTeXbuild
fi
mkdir LaTeXbuild
cd LaTeXbuild
xsltproc --xinclude ../mathbook/xsl/mathbook-latex.xsl ../nazgand-book.xml
cd ..

