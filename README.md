
# A Set of Tools for the User Authorization Query (UAQ) Problem

## An Efficient UAQ Solver: AQUA

AQUA is an efficient solver for the User Authorization Query (UAQ) problem in Role-Based Access Control (RBAC). The UAQ problem amounts to determining a set of roles granting a given set of per- missions, satisfying a collection of authorisation constraints (most notably Dynamic Mutually-Exclusive Roles, DMER) and achieving some optimization objective, i.e. seeking min/max/any number of roles to activate and/or permissions to grant. AQUA supports the enforcement of a wide class of DMER constraints as well as several types of optimization objectives (namely, min/max/any number of roles to activate, min/max/any number of permissions to grant, and a combinations thereof).

### Executables
AQUA executable files can be generated as follows:
~~~~
g++ -DSMART_MER_ENCODING solve_uaq.c -o solve_uaq_smart.exe (this uses sinz's encoding of mer constraints)
g++ -DNAIVE_MER_ENCODING solve_uaq.c twiddle.c -o solve_uaq_naive.exe (this uses the naive encoding of mer constraints)
~~~~

Download the Cardinality Constraints encoding [here](http://www-sr.informatik.uni-tuebingen.de/~sinz/CardConstraints/CardConstraints.zip),  unzip in the main folder (CC) and run the make command. In order the compilation to succeed,
you may have to add the directives 
~~~~
#include <stdio.h>  
~~~~
in SeqCounter.cpp
and
~~~~
#include <stdio.h>
#include <cstring>
~~~~
in ParCounter.cpp.

Plus the following solvers (even if not all of them are used using the current settings):

* minisat.exe  (the MINISAT SAT solver)
* CCLS2014-Bounded.exe
* CCLS_to_akmaxsat.exe
* WPM1-2012
* qmaxsat14.04auto-glucose3_static
* /usr/bin/java -jar %s/sat4j-maxsat.jar
* maxsatz2013f
* WPM1-2012

You must also install runsolver (from [here](http://www.cril.univ-artois.fr/~roussel/runsolver/))
if you would like to do benchmarking with the UAQ solver.

`solve_uaq.c` assumes two environmental variables: 
* CCPATH (set to the path of the directory containing Sinz' executables) and
* SATSOLVERPATH (set to the path of the directory containing the executables of the SAT solvers).

For instance, I have put the following two lines in my `.bashrc` file:
~~~~
export CCPATH=/home/armando/work/st/CC
export SATSOLVERPATH=/home/armando/work/st/CC
~~~~

## Benchmarking
The main script for benchmarking related functionality is `workbench.exe`
It can be invoked in the following way:

`./workbench.exe make_templates <spec-file> `

`spec-file` sets the values of the parameters using the following format:
~~~~
--INSTANCES_MAX=10 --SESSIONS_MAX=5 --ROLES_MIN=25 --ROLES_MAX=300 --ROLES_STEP=25 --PERMS_PER_ROLE=8 --ROLES_PER_CONSTR=5 --CONSTR_RATIO=10 --MER_BOUND=3 --PERMS_LB=50
~~~~

Once you have generated the templates, you can generate the instances, the encodings and apply the MAXSAT solvers as follows:

~~~~
./workbench.exe make_instances <spec-file> 
./workbench.exe encode <spec-file> 
./workbench.exe solve <spec-file> 
~~~~

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

```
NR	TMedian	TMean	NV	NC	PUNSAT
 20	 0.002	 0.005	793	1515	0.70
```
means that 70% of the instances with NR=20 are UNSAT.

workbench.exe assumes the existence of AQUA executable files in the current directory, plus the template generator:
~~~~
g++ make_templates.c -o make_templates.exe
~~~~

### References :
AQUA system description :
1. Alessandro Armando, Giorgia A. Gazzarata, Fatih Turkmen:
AQUA: An Efficient Solver for the User Authorization Query Problem. SACMAT 2020: 153-154

PMaxSAT Encoding and Other Details

2. Alessandro Armando, Giorgia Gazzarata, Fatih Turkmen:
Benchmarking UAQ Solvers. SACMAT 2020: 145-152

3. Alessandro Armando, Silvio Ranise, Fatih Turkmen, Bruno Crispo:
Efficient run-time solving of RBAC user authorization queries: pushing the envelope. CODASPY 2012: 241-248



### NOTES :
* The spec files need to be in *.spec extension.
