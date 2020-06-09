# RoundingSat

RoundingSat is a pseudo-Boolean SAT solver for optimization and decision problems.

## Compilation

Download soplex at
https://soplex.zib.de/download.php?fname=soplex-5.0.0.tgz and place
the downloaded file in the root directory of roundingsat,
alternatively the location can also be configured see `cd build; cmake -L ..` for more information.

In the root directory of roundingsat:

    cd build
    cmake -DCMAKE_BUILD_TYPE=Release ../
    make

If you also want a debug build, just create another build folder and
call cmake from there using `-DCMAKE_BUILD_TYPE=Debug`.

## Usage

For the input formats, see [here](InputFormats.md).

Download OPB files:

    curl http://www.cril.univ-artois.fr/PB12/bench12/PB12-DEC-SMALLINT-LIN.tar | tar xv

Try on an example instance which is solved quickly:

    bzcat ./PB12/normalized-PB12/DEC-SMALLINT-LIN/sroussel/ShortestPathBA/normalized-BeauxArts_K76.opb.bz2 | ./roundingsat

## Citation

[Elffers and Nordström, 2018] J. Elffers and J. Nordström. Divide and Conquer: Towards Faster Pseudo-Boolean Solving. *IJCAI 2018*, 1291-1299.

## Quick debug tests with VeriPB

The following commands run roundingsat_debug for one second on a list of relatively small decision and optimization instances, and verifies the generated proofs with VeriPB (https://github.com/StephanGocht/VeriPB).

    `cd test`
    `./test_proofs.sh 1`

To run with a timeout of, say, 10s run

    `./test_proofs.sh 10`
