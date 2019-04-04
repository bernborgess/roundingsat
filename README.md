# plane-sat

plane-sat is a pseudo-boolean SAT solver.

## Compilation

The solver currently consists of a single file which can be compiled on Linux. It uses some c++11 constructs.

    g++ -o plane-sat plane-sat.cc -std=c++11 -O3

## Usage

For the input format, see [here](InputFormats.md).

Download OPB files:

    curl http://www.cril.univ-artois.fr/PB12/bench12/PB12-DEC-SMALLINT-LIN.tar | tar xv
    
Try on an example instance which is solved quickly:

    bzcat ./PB12/normalized-PB12/DEC-SMALLINT-LIN/sroussel/ShortestPathBA/normalized-BeauxArts_K76.opb.bz2 | ./plane-sat
