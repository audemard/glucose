cd pfactory
make clean
make clean-am
cd ..
cmake --build . --target clean -- -j 16
