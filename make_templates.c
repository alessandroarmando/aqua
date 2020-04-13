#include<unistd.h>
#include<stdio.h>
#include<string.h>
#include<stdlib.h>
#include <getopt.h>
#include <sys/types.h>
#include <sys/stat.h>
using namespace std;

#define max(x,y) ((x>y)?x:y)

int INSTANCES_MAX=-1;
int SESSIONS_MAX=-1;
int ROLES_MIN=-1;
int ROLES_MAX=-1;
int ROLES_STEP=-1;
int PERMS_PER_ROLE=-1;
int ROLES_PER_PERM=-1;
int ROLES_PER_CONSTR=-1;
int CONSTR_RATIO=-1;
int MER_BOUND=-1;
const int SEED=12345;
char filename[1000];

int PERMS_MAX;
int PERMS_LB;
int PERMS_LB_START;
int PERMS_LB_STEP;
int PERMS_UB;

// Generate a random combination of values.
// From Jon Bentley's Programming Pearls column "A sample of Brilliance"
// Set s to a random combination of m elements ranging in the interval [0..n-1]
// Clearly the size of s must be (at least) m.
/* initialize set S to empty */
/* for J := N-M + 1 to N do */
/*     T := RandInt(1, J) */
/*     if T is not in S then */
/*         insert T in S */
/*     else */
/*         insert J in S */
void rand_combination (int s[], int m, int n) {
  int j;
  for(j=0;j<m;j++) {
    int t,k;
    t=rand()%(n-m+j);
    for(k=0;k<j&&s[k]!=t;k++);
    if(k==j)
      s[j]=t;
    else
      s[j]=n-m+j;
  }
}

void print_usage(char cmd[]) {
  printf("Usage: %s \n",cmd);
}

void check_option_int(const char name[], int x, const char *const msg) {
  printf("%s=%d\n",name,x);
  if(x<0) {
    fprintf(stderr,"Error: %s  must be set to %s!\n",name,msg);
    exit(1);
  }
}

void check_option_sscope(char *x) {
  printf("SSCOPE=%s\n",x);
  if(x==NULL || (strcmp(x,"ss")!=0 && strcmp(x,"ms")!=0)) {
    fprintf(stderr,"Error: SSCOPE must be set to 'ss' or 'ms'!\n");
    exit(1);
  }
}

void check_option_tscope(char *x) {
  printf("TSCOPE=%s\n",x);
  if(x==NULL || (strcmp(x,"d")!=0 && strcmp(x,"h")!=0)) {
    fprintf(stderr,"Error: TSCOPE must be set to 'd' or 'h'!\n");
    exit(1);
  }
}

void check_option_dir(char *x) {
  printf("DIR=%s\n",x);
  if(x==NULL) {
    fprintf(stderr,"Error: DIR must be set to the name of a new directory!\n");
    exit(1);
  }
}

int main(int argc, char *argv[]) {
  int r, p, num_roles, l;
  FILE *fp;

  printf("hue-1");

  int opt= 0;
  static struct option long_options[] = {
    {"INSTANCES_MAX",  required_argument,       0,  0 },
    {"SESSIONS_MAX",  required_argument,       0,  1 },
    {"ROLES_MIN",  required_argument,       0,  2 },
    {"ROLES_MAX",  required_argument,       0,  3 },
    {"ROLES_STEP",  required_argument,       0,  4 },
    {"PERMS_MAX",  required_argument,       0,  5 },
    {"PERMS_LB",  required_argument,       0,  6 },
    {"PERMS_UB",  required_argument,       0,  7 },
    {"PERMS_PER_ROLE",  required_argument,       0,  8 },
    {"ROLES_PER_PERM",  required_argument,       0,  9 },
    {"ROLES_PER_CONSTR",  required_argument,       0,  10 },
    {"MER_BOUND",  required_argument,       0,  11 },
    {"CONSTR_RATIO",  required_argument,       0,  12 },
    {"SSCOPE",  required_argument,       0,  13 },
    {"TSCOPE",  required_argument,       0,  14 },
    {"DIR",  required_argument,       0,  15 },
    {"PERMS_LB_START",  required_argument,       0,  16 },
    {"PERMS_LB_STEP",  required_argument,       0,  17 },
    {0,           0,                 0,  0   }
  };

  int long_index =0;
  char *DIR=NULL, *SSCOPE=NULL, *TSCOPE=NULL;
  while ((opt = getopt_long(argc, argv,"", long_options, &long_index )) != -1) {
    switch (opt) {
    case 0 : INSTANCES_MAX = atoi(optarg); break;
    case 1 : SESSIONS_MAX = atoi(optarg); break;
    case 2 : ROLES_MIN = atoi(optarg); break;
    case 3 : ROLES_MAX = atoi(optarg); break;
    case 4 : ROLES_STEP = atoi(optarg); break;
    case 5 : PERMS_MAX = atoi(optarg); break;
    case 6 : PERMS_LB = atoi(optarg); break;
    case 7 : PERMS_UB = atoi(optarg); break;
    case 8 : PERMS_PER_ROLE = atoi(optarg); break;
    case 9 : ROLES_PER_PERM = atoi(optarg); break;
    case 10 : ROLES_PER_CONSTR = atoi(optarg); break;
    case 11 : MER_BOUND = atoi(optarg); break;
    case 12 : CONSTR_RATIO = atoi(optarg); break;
    case 13 : SSCOPE = optarg; break;
    case 14 : TSCOPE = optarg; break;
    case 15 : DIR = optarg; break;
    case 16 : PERMS_LB_START = atoi(optarg); break;
    case 17 : PERMS_LB_STEP = atoi(optarg); break;
    default: print_usage(argv[0]); 
      exit(EXIT_FAILURE);
    }
  }

  check_option_int("INSTANCES_MAX",INSTANCES_MAX,"a positive integer");
  check_option_int("SESSIONS_MAX",SESSIONS_MAX,"a positive integer");
  check_option_int("ROLES_MIN",ROLES_MIN,"a positive integer");
  check_option_int("ROLES_MAX",ROLES_MAX,"a positive integer");
  check_option_int("ROLES_STEP",ROLES_STEP,"a positive integer");
  check_option_int("PERMS_MAX",PERMS_MAX,"a positive integer");
  check_option_int("PERMS_LB",PERMS_LB,"a positive integer");
  check_option_int("PERMS_UB",PERMS_UB,"a positive integer");
  check_option_int("PERMS_PER_ROLE",PERMS_PER_ROLE,"a positive integer");
  check_option_int("ROLES_PER_PERM",ROLES_PER_PERM,"a positive integer");
  check_option_int("ROLES_PER_CONSTR",ROLES_PER_CONSTR,"a positive integer");
  check_option_int("CONSTR_RATIO",CONSTR_RATIO,"a positive integer");
  check_option_int("MER_BOUND",MER_BOUND,"a positive integer");
  check_option_sscope(SSCOPE);
  check_option_tscope(TSCOPE);
  check_option_int("PERMS_LB_START",PERMS_LB_START,"a positive integer");
  check_option_int("PERMS_LB_STEP",PERMS_LB_STEP,"a positive integer");
  check_option_dir(DIR);

  printf("hue0");
  fflush(stdout);
    
  /* printf("\n>>PERMS_MAX=%d<<\n",PERMS_MAX); */
  int i, j;
  int *rs=new int[ROLES_MAX];

  struct stat st = {0};
  if (stat(DIR, &st) == -1) {
    mkdir(DIR, 0700);
  }
  else {
    fprintf(stderr,"Warning: directory %s already exists!\n",DIR);
    exit(1);
  }
    
  sprintf(filename,"%s/pb.spec",DIR);
  fp=fopen(filename,"w");
  fprintf(fp,"ROLES_MIN %d\n",ROLES_MIN);
  fprintf(fp,"ROLES_MAX %d\n",ROLES_MAX);
  fprintf(fp,"ROLES_STEP %d\n",ROLES_STEP);
  fprintf(fp,"PERMS_LB %d\n",PERMS_LB);
  fprintf(fp,"PERMS_LB_START %d\n",PERMS_LB_START);
  fprintf(fp,"PERMS_LB_STEP %d\n",PERMS_LB_STEP);
  fprintf(fp,"INSTANCES %d\n",INSTANCES_MAX);
  fprintf(fp,"MER_BOUND %d\n",MER_BOUND);
  fprintf(fp,"ROLES_PER_CONSTR %d\n",ROLES_PER_CONSTR);
  fprintf(fp,"SSCOPE %s\n",SSCOPE);
  fprintf(fp,"TSCOPE %s\n",TSCOPE);
  fclose(fp);

  int nr;

  for(num_roles=ROLES_MIN;num_roles<=ROLES_MAX;num_roles+=ROLES_STEP) {
    srand(SEED);
    printf("==>num_roles=%d\n",num_roles);fflush(stdout);
    /* PERMS_MAX=5*num_roles; */
    /* PERMS_MAX=1000+2*num_roles; */
    /* PERMS_MAX=500+3*num_roles; */
    PERMS_MAX=50+num_roles;
    /* PERMS_LB=5+PERMS_MAX/30; */
    /* PERMS_UB=(5*PERMS_MAX)/6; */
    /* PERMS_LB=100; */
    /* PERMS_UB=70; */
    int **pax=new int*[num_roles];
    pax[0]=new int[num_roles*PERMS_MAX];
    int plb;
    for(plb=PERMS_LB_START;plb<=PERMS_LB;plb+=PERMS_LB_STEP) {
      for(i=1;i<num_roles;i++)
	pax[i]=pax[i-1]+PERMS_MAX;
      /* int *assigned_permission; */
      /* printf("\nassigned_permission[%d]\n",PERMS_MAX); */
      /* assigned_permission=new int[PERMS_MAX]; */
      int CONSTR_MAX=max(1,num_roles/CONSTR_RATIO);
      printf("Generating instances with %d roles and plb=%d:",num_roles,plb);fflush(stdout);
      for(l=0;l<INSTANCES_MAX;l++) {
	printf("-->l=%d",l);fflush(stdout);
	for(r=0;r<num_roles;r++) {
	  /* printf("\nInitializing:\n");fflush(stdout); */
	  for(i=0;i<PERMS_MAX;i++) {
	    /* printf("pax[%d][%d] ",r,i);fflush(stdout); */
	    pax[r][i]=0;
	  }
	}
	/* for(j=0;j<PERMS_MAX;j++) */
	/* 	assigned_permission[j]=0; */
	printf(" %d",l);fflush(stdout);
	sprintf(filename,"%s/%s-%s-%d-%d-%d-template.uaq",DIR,SSCOPE,TSCOPE,num_roles,plb,l);
	fp = fopen(filename,"w");
	fprintf(fp,"users : alice ;\n");
	fprintf(fp,"roles : ");
	for(r=1;r<=num_roles;r++)
	  fprintf(fp,"r%d ",r);
	fprintf(fp,";\n");
	fprintf(fp,"perms : ");
	for(p=1;p<=PERMS_MAX;p++)
	  fprintf(fp,"p%d ",p);
	fprintf(fp,";\n");
	int s;
	fprintf(fp,"sesss :");
	for(s=0;s<SESSIONS_MAX;s++)
	  fprintf(fp," s%d",s+1);
	fprintf(fp," ;\n\n");
	for(s=0;s<SESSIONS_MAX;s++)
	  fprintf(fp,"sof [ s%d ] : alice ;\n",s+1);
	fprintf(fp,"--\n");
	fprintf(fp,"ua [ alice ] : ");
	for(r=1;r<=num_roles;r++)
	  fprintf(fp,"r%d ",r);
	fprintf(fp,";\n");
	fprintf(fp,"--\n");

	printf("hue3");fflush(stdout);
	int count;
	count=PERMS_PER_ROLE;
	for(r=0;r<num_roles;r++) {
	  while(count>0) {
	    int t;
	    t=rand()%PERMS_MAX;
	    /* printf("checking (%d,%d)\n",r,t);fflush(stdout); */
	    if(pax[r][t]==0) {
	      pax[r][t]=1;
	      count--;
	    }
	  }
	  count=PERMS_PER_ROLE;
	}	  
	printf("hue4\n");fflush(stdout);
	for(i=0;i<PERMS_MAX;i++) {
	  count=ROLES_PER_PERM;
	  for(r=0;count>0&&r<num_roles;r++)
	    if(pax[r][i]==1) count--;
	  while(count>0) {
	    int t;
	    t=rand()%num_roles;
	    if(pax[t][i]==0) {
	      /* printf("(%d,%d) set\n",t,i); */
	      pax[t][i]=1;
	      count--;
	    }
	  }
	}
	printf("hue5\n");fflush(stdout);

	/* for(r=0;r<num_roles;r++) { */
	/* 	for(i=0;i<PERMS_MAX;i++) */
	/* 	  printf("%d ",pax[r][i]); */
	/* 	printf("\n"); */
	/* } */

	for(r=0;r<num_roles;r++) {
	  fprintf(fp,"pa [ r%d ] : ",r+1);
	  for(i=0;i<PERMS_MAX;i++)
	    if(pax[r][i]==1)
	      fprintf(fp,"p%d ",i+1);
	  fprintf(fp,";\n");
	}
	fprintf(fp,"--\n");
	fprintf(fp,"--\n");
	fprintf(fp,"--\n");
	for(i=0;i<CONSTR_MAX;i++) {
	  fprintf(fp,"mer %s %s %d ",SSCOPE,TSCOPE,MER_BOUND);
	  rand_combination(rs,ROLES_PER_CONSTR,num_roles);
	  for(r=0;r<ROLES_PER_CONSTR;r++)
	    fprintf(fp,"r%d ",rs[r]+1);
	  fprintf(fp,";\n");
	}
	fprintf(fp,"--\n");
	/* printf(">>>>>>>>>>>>>QUERY s1 %s GRANT\n ",OBJ); */
	fprintf(fp,"QUERY s1 %s GRANT ","MIN");
	for(i=0,j=0;i<plb&&j<PERMS_MAX;j++) {
	  for(r=0;pax[r][j]==0&&r<num_roles;r++);
	  if(pax[r][j]==1)
	    fprintf(fp,"p%d ",j+1);
	  i++;
	}
	fprintf(fp,"DENY ");
	/* for(i=0;i<PERMS_MAX-PERMS_UB&&j<PERMS_MAX;j++) { */
	/* 	if(assigned_permission[j]==1) { */
	/* 	  fprintf(fp,"p%d ",j+1); */
	/* 	  i++; */
	/* 	} */
	/* } */
	fprintf(fp,";\n");
	fclose(fp);
      }
    }
    printf("\n");
    /* delete[] assigned_permission; */
    delete[] pax[0];
    delete[] pax;
    printf("<==num_roles=%d\n",num_roles);
  }
  delete[] rs;
}
