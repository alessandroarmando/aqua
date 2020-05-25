
The main script is workbench.exe
It can be invoked in the following way:

`./workbench.exe make_templates <spec-file> `

spec-file sets the values of the parameters using the following format:
--INSTANCES_MAX=10 --SESSIONS_MAX=5 --ROLES_MIN=25 --ROLES_MAX=300 --ROLES_STEP=25 --PERMS_PER_ROLE=8 --ROLES_PER_CONSTR=5 --CONSTR_RATIO=10 --MER_BOUND=3 --PERMS_LB=50

Once you have generated the templates, you can generate the instances, the encodings and apply the MAXSAT solvers as follows:

./workbench.exe make_instances <spec-file> 
./workbench.exe encode <spec-file> 
./workbench.exe solve <spec-file> 

where <spec-file> is the same specification files used to generate the templates.

The above commands create the following folders: <spec-file>-ss-d, <spec-file>-ss-h, <spec-file>-ms-d, <spec-file>-ms-h
which are in turn populated by the files containing the uaq instances and two sub-folders, named "naive" and "smart" containing
the exponential encoding and the encodings based on sinz' code respectively.  The results of the experimental results live 
within these subfolders in the files

summary-{encoding,solving}-{ANY,MIN,MAX}.txt
plot-{encoding,solving}-{ANY,MIN,MAX}.txt

The former contain the data for each instance (T=time, V=variables, C=clauses, Status={SAT,UNSAT}).
The latter contain the median and mean time, the number of variables and the number of clauses, and finally the percentage of unsat instances.
For insance,

NR	TMedian	TMean	NV	NC	PUNSAT
 20	 0.002	 0.005	793	1515	0.70

means that 70% of the instances with NR=20 are UNSAT.

workbench.exe assumes the existence of a number of executable files in the current directory.  
These files can be generate as follows:
g++ make_templates.c -o make_templates.exe
g++ -DSMART_MER_ENCODING solve_uaq.c -o solve_uaq_smart.exe (this uses sinz's encoding of mer constraints)
g++ -DNAIVE_MER_ENCODING solve_uaq.c twiddle.c -o solve_uaq_naive.exe (this uses the naive encoding of mer constraints)

Download
http://www-sr.informatik.uni-tuebingen.de/~sinz/CardConstraints/CardConstraints.zip
unzip in the main folder (CC) and run the make command.  (I had to add the directives 
~~~~
#include <stdio.h>  
in SeqCounter.cpp
~~~~
and
~~~~
#include <stdio.h>
#include <cstring>
in ParCounter.cpp
~~~~
for the compilation to succeed.)

Plus the following solvers (even if not all of them are used using the current settings):
minisat.exe  (the MINISAT SAT solver)
CCLS2014-Bounded.exe
CCLS_to_akmaxsat.exe
WPM1-2012
qmaxsat14.04auto-glucose3_static
/usr/bin/java -jar %s/sat4j-maxsat.jar
maxsatz2013f
WPM1-2012

You must also install runsolver (from http://www.cril.univ-artois.fr/~roussel/runsolver/)

solve_uaq.c assumes two environmental variables: 
- CCPATH (set to the path of the directory containing Sinz' executables) and
- SATSOLVERPATH (set to the path of the directory containing the executables of the SAT solvers).

For instance, I have put the following two lines in my .bashrc file:
export CCPATH=/home/armando/work/st/CC
export SATSOLVERPATH=/home/armando/work/st/CC

NOTES :
- The spec files need to be in *.spec extension (why?).
- Do not forget to mention twiddle. 
