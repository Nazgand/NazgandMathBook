#!/bin/bash

while inotifywait -e close_write ./*.xml
do
	echo 'xml file change detected.'
	./build.sh
done