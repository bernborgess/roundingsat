/***********************************************************************
Copyright (c) 2014-2020, Jan Elffers
Copyright (c) 2019-2020, Jo Devriendt

Parts of the code were copied or adapted from MiniSat.

MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
           Copyright (c) 2007-2010  Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
***********************************************************************/

#pragma once

struct Stats {
	long long NTRAILPOPS=0, NWATCHLOOKUPS=0, NWATCHLOOKUPSBJ=0, NWATCHCHECKS=0, NPROPCHECKS=0, NADDEDLITERALS=0;
	long long NCONFL=0, NDECIDE=0, NPROP=0, NPROPCLAUSE=0, NPROPCARD=0, NPROPWATCH=0, NPROPCOUNTING=0;
	long long NWATCHED=0, NCOUNTING=0;
	__int128 LEARNEDLENGTHSUM=0, LEARNEDDEGREESUM=0;
	long long NCLAUSESLEARNED=0, NCARDINALITIESLEARNED=0, NGENERALSLEARNED=0;
	long long NGCD=0, NCARDDETECT=0, NCORECARDINALITIES=0, NCORES=0, NSOLS=0;
	long long NWEAKENEDNONIMPLYING=0, NWEAKENEDNONIMPLIED=0;
	long long NRESTARTS=0, NCLEANUP=0;

	inline long long getDetTime(){
		return 1+NADDEDLITERALS+NWATCHLOOKUPS+NWATCHLOOKUPSBJ+NWATCHCHECKS+NPROPCHECKS+NPROP+NTRAILPOPS+NDECIDE;
	}
};