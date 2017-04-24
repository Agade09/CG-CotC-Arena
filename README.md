# CG-CotC-Arena
Arena program to play games between two Coders of the Carribbean AIs from Codingame. 
**Linux only**.
**Does not handle MOVE**.

## Usage:
* Compile the Arena program with the given Makefile
* Have two of your AIs' executable binaries/scripts in the same folder
* Run the Arena program with the names of the AI executables as command line parameters. e.g: Arena V13 V12

## Optional:
* Specify the number of threads as a command line parameter. e.g: Arena V13 V12 2
* Set timeout behavior on or off via the "constexpr bool Timeout" variable. This can be useful as I've noticed timeouts if the computer is being used for something else.

## Notes:
* The error bars on the win rate are approximate. The approximation is good around 50% win rate.
