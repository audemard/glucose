#!/bin/csh
if ( $#argv == 1) then
if ( $#argv == 1 && $argv[1] == "all" ) then
  cd pfactory
  ./bootstrap
  ./configure
  make -j
  cd ..
else
  if( $#argv == 1 ) then
    echo "usage : ./build.sh [all]"
    exit
  endif
endif
endif

cmake -DCMAKE_BUILD_TYPE=Release -G "Unix Makefiles" .
cmake --build . --target glucose -- -j 8
