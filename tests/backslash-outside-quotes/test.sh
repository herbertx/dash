#!./src/dash
a=/b/c/*
b=\\
echo ${a%$b*}
