#include<unistd.h>
#include<stdio.h>
#include<string.h>
#include<stdlib.h>
#ifdef __linux__ 
#include<linux/limits.h>
#else
#include<limits.h>
#endif
#include <libgen.h>
#include<getopt.h>
#include"twiddle.h"
using namespace std;

#define abs(x) ((x)<0 ? -(x) : (x))
#define sign(x) ((x)<0 ? '-' : '+')
#define MIN(a,b) (((a)<(b))?(a):(b))
#define MAX(a,b) (((a)>(b))?(a):(b))

// Roles are assigned propositional variables in the interval [1..num_roles]
// Permissions are assigned propositional variables in the interval [num_roles+1..num_roles+num_perms]]
// Auxiliary variables are assigned propositional variables in the interval [num_roles+num_perms+1..num_roles+num_perms+num_aux]
// For instance, if num_roles=5, num_perms=10, and num_aux=3, then
// Roles are assigned propositional variables 1, 2, ..., 5
// Permissions are assigned propositional variables 6, 7, ..., 15
// Auxiliary variables are assigned propositional variables 16, 17, 18.

#define rolep(x) ((x>=0 && x<num_roles))
#define permp(x) ((x>=num_roles && x<(num_roles+num_perms)))
#define auxp(x) ((x>=(num_roles+num_perms) && x<(num_roles+num_perms+num_aux)))
#define r2a_role(x) ((x+1))
#define r2a_perm(x) ((num_roles+x+1))
#define r2a_aux(x) ((num_roles+num_perms+x+1))
#define a2r_role(x) ((x-1))
#define a2r_perm(x) ((x-num_roles-1))
#define a2r_aux(x) ((x-num_roles-num_perms-1))

const int USERS_MAX=1000;
const int ROLES_PERMS_MAX=20000;
const int ROLES_MAX=ROLES_PERMS_MAX;
const int PERMS_MAX=ROLES_PERMS_MAX; // PERMS_MAX must be equal to ROLES_MAX due to programming trick in read_relations formal parameter
const int SESSS_MAX=1000;
const int AUX_MAX=100000;
const int ROLES_MAX_PER_CONSTR=200;
const int CONSTRS_MAX=200;
int GENERATE;
int NUM_SLACK_VARS;
char SATSolverCmdString[500];

FILE *fp_spec, *fp_enc, *fp_debug;

typedef enum {any, min, max} obj_type;
typedef enum {ss, ms} sscope_type;
typedef enum {d, h} tscope_type;
typedef struct 
{ sscope_type sscope; 
  tscope_type tscope;
  int n;
  int rs[ROLES_MAX_PER_CONSTR];
  int rs_card;
} mer_type;
mer_type mer[CONSTRS_MAX];

const char *sscope_name[] = { "ss", "ms" };
const char *tscope_name[] = { "d", "h" };

obj_type OBJ;

/* int DEBUG=1; */

char *ccpath, *satsolverpath;
/* char ccpath[]="/home/armando/work/st/CC"; */
/* char satsolverpath[]="/home/armando/work/st/CC"; */
/* char ccpath[]="/home/fturkmen/workspaceC++/AlessandroImplementation/SVN"; */
/* char satsolverpath[]="/home/fturkmen/workspaceC++/AlessandroImplementation/SVN"; */
/* char ccpath[]="."; */
/* char satsolverpath[]="."; */
char *rname[ROLES_MAX], *uname[USERS_MAX], *pname[PERMS_MAX], *sname[SESSS_MAX], *xname[AUX_MAX];
int num_roles=0;
int num_users=0;
int num_perms=0;
int num_sesss=0;
int num_mers=0;
int num_aux=0;
int num_clauses=0;

int sid;
int ua[USERS_MAX][ROLES_MAX];
int pa[ROLES_MAX][PERMS_MAX];
int sof[SESSS_MAX];
int msd_aux[ROLES_MAX], ssh_aux[ROLES_MAX], msh_aux[ROLES_MAX];
int grant[PERMS_MAX], deny[PERMS_MAX];
int once_aux[SESSS_MAX][ROLES_MAX];
int yesterday_aux[SESSS_MAX][ROLES_MAX];

char dimacsfile[PATH_MAX+1], resfile[PATH_MAX+1], errfile[PATH_MAX+1];
char specfile[PATH_MAX+1], newspecfile[PATH_MAX+1];
char *bname;

void fscant(FILE *fp, const char t[]) {
  char s[10000];
  fscanf(fp,"%s",s);
  if(strcmp(s,t)!=0) {
    fprintf(stderr,"Syntax error: expected %s, found %s.\n",t,s);
    exit(EXIT_FAILURE);
  }
}

char *strip_prefix(char tgt[], char src[]) {
  int i;
  for(i=0;(src[i]!='.' && src[i]!='\0');i++)
    tgt[i]=src[i];
  if(src[i]=='\0') {
    fprintf(stderr,"strip_prefix: filename %s does not contain a '.'\n",src);
    exit(EXIT_FAILURE);
  }
  tgt[i]='\0';
  return src+i;
}

int aux_for_once(int s, int r) {
  if(once_aux[s][r]>=0)
    return once_aux[s][r];
  once_aux[s][r]=num_aux++;
  return num_aux-1;
}

int aux_for_yesterday(int s, int r) {
  if(yesterday_aux[s][r]>=0)
    return yesterday_aux[s][r];
  yesterday_aux[s][r]=num_aux++;
  return num_aux-1;
}

void read_entities (char const keyword[], char *name[], int &pn) {
  char token[60];
  fscant(fp_spec,keyword);
  /* printf("Reading %s declaration\n",keyword); */
  fscant(fp_spec,":");
  fscanf(fp_spec,"%s",token);
  /* printf("reading role=%s, strcmp=%d\n",token,strcmp(token,";")); */
  while(strcmp(token,";")!=0) {
    /* printf("reading identifier=%s\n",token); */
    name[pn]=new char[strlen(token)+1];
    strcpy(name[pn],token);
    pn++;
    fscanf(fp_spec,"%s",token);
  }
  //printf(" Elem : %s,  Number : %d\n", keyword, pn);
}

void read_relations(char const keyword[], char *xname[], char *yname[], int r[][ROLES_PERMS_MAX], int m, int n) {
  int i,j;
  char token[60];
  for(i=0;i<m;i++)
    for(j=0;j<n;j++)
      r[i][j]=-1;
  fscanf(fp_spec,"%s",token);
  while(strcmp(token,"--")!=0) {
    /* printf("1 - here is token=%s\n",token); */
    if(strcmp(token,keyword)!=0) {
      fprintf(stderr,"Syntax error: expected keywork %s, found %s.\n",keyword,token);
      exit(EXIT_FAILURE);
    }
    /* printf("Reading %s declaration\n",keyword); */
    fscant(fp_spec,"[");
    fscanf(fp_spec,"%s",token);
    for(i=0;(i<m && strcmp(xname[i],token)!=0);i++);
      /* printf("xname[%d]=%s\n",i,xname[i]); */
    if(i==m) {
      fprintf(stderr,"read_relations: Identifier %s not declared.\n", token);
      exit(EXIT_FAILURE);
    }
    fscant(fp_spec,"]");
    fscant(fp_spec,":");
    fscanf(fp_spec,"%s",token);
    /* printf("reading role=%s, strcmp=%d\n",token,strcmp(token,";")); */
    while(strcmp(token,";")!=0) {
      /* printf("reading identifier=%s\n",token); */
      for(j=0;(j<n && strcmp(yname[j],token)!=0);j++);
      if(j==n) {
	fprintf(stderr,"read_relations: Identifier %s not declared.\n", token);
	exit(EXIT_FAILURE);
      }
      r[i][j]=1;
      fscanf(fp_spec,"%s",token);
    }
    fscanf(fp_spec,"%s",token);
  }
}

void read_yo(char const keyword[], char *xname[], char *yname[], int r[][ROLES_PERMS_MAX], int m, int n) {
  int i,j;
  char token[60];
  for(i=0;i<m;i++)
    for(j=0;j<n;j++)
      r[i][j]=-1;
  fscanf(fp_spec,"%s",token);
  while(strcmp(token,"--")!=0) {
    /* printf("1 - here is token=%s\n",token); */
    if(strcmp(token,keyword)!=0) {
      fprintf(stderr,"Syntax error: expected keywork %s, found %s.\n",keyword,token);
      exit(EXIT_FAILURE);
    }
    /* printf("Reading %s declaration\n",keyword); */
    fscant(fp_spec,"[");
    fscanf(fp_spec,"%s",token);
    for(i=0;(i<m && strcmp(xname[i],token)!=0);i++);
      /* printf("xname[%d]=%s\n",i,xname[i]); */
    if(i==m) {
      fprintf(stderr,"read_yo: Identifier %s not declared.\n", token);
      exit(EXIT_FAILURE);
    }
    fscant(fp_spec,"]");
    fscant(fp_spec,":");
    fscanf(fp_spec,"%s",token);
    /* printf("reading role=%s, strcmp=%d\n",token,strcmp(token,";")); */
    while(strcmp(token,";")!=0) {
      /* printf("reading identifier=%s\n",token); */
      for(j=0;(j<n && strcmp(yname[j],token)!=0);j++);
      if(j==n) {
	fprintf(stderr,"read_yo: Identifier %s not declared.\n", token);
	exit(EXIT_FAILURE);
      }
      if(r==once_aux) {
	r[i][j]=aux_for_once(i,j);
      }
      else if (r==yesterday_aux) {
	r[i][j]=aux_for_yesterday(i,j);
	/* printf("yesterday[%d][%d]=%d\n",i,j,r[i][j]); */
      }
      else {
	fprintf(stderr,"read_yo: argument 'r' must be either once_aux or yesterday_aux.\n");
      }
      fscanf(fp_spec,"%s",token);
    }
    fscanf(fp_spec,"%s",token);
  }
}

void read_attribute (char const keyword[], char *xname[], char *yname[], int r[], int m, int n) {
  int i, j;
  char token[60];
  for(i=0;i<m;i++)
    r[i]=-1;
  fscanf(fp_spec,"%s",token);
  while(strcmp(token,"--")!=0) {
    /* printf("1 - here is token=%s\n",token); */
    if(strcmp(token,keyword)!=0) {
      fprintf(stderr,"Syntax error: expected keywork %s, found %s.\n",keyword,token);
      exit(EXIT_FAILURE);
    }
    /* printf("Reading %s declaration\n",keyword); */
    fscant(fp_spec,"[");
    fscanf(fp_spec,"%s",token);
    for(i=0;(i<m && strcmp(xname[i],token)!=0);i++);
    /*   printf("xname[%d]=%s\n",i,xname[i]); */
    /* printf("Found xname[%d]=%s !!!\n",i,xname[i]); */
    if(i==m) {
      fprintf(stderr,"read_attribute: Identifier %s not declared.\n", token);
      exit(EXIT_FAILURE);
    }
    fscant(fp_spec,"]");
    fscant(fp_spec,":");
    fscanf(fp_spec,"%s",token);
    for(j=0;(j<n && strcmp(yname[j],token)!=0);j++);
    /* printf("Found yname[%d]=%s !!!\n",j,yname[j]); */
    if(j==n) {
      fprintf(stderr,"read_attribute: Identifier %s not declared.\n", token);
      exit(EXIT_FAILURE);
    }
    r[i]=j;
    fscant(fp_spec,";");
    fscanf(fp_spec,"%s",token);
  }
}

void print_entities(FILE *fp, char const keyword[], char *name[], int pn) {
  int r;
  fprintf(fp,"%s : ",keyword);
  for(r=0;r<pn;r++)
    fprintf(fp,"%s ", name[r]);
  fprintf(fp," ;\n");
}

void print_relations(FILE *fp,char const keyword[], char *xname[], char *yname[], int r[][ROLES_PERMS_MAX], int m, int n) {
  int i, j;
  for(i=0;i<m;i++) {
    fprintf(fp,"%s [ %s ] :",keyword,xname[i]);
    for(j=0;j<n;j++)
      if(r[i][j]>=0)
	fprintf(fp," %s",yname[j]);
    fprintf(fp," ;\n");
  }
}

void print_yo(FILE *fp,char const keyword[], char *xname[], char *yname[], int r[][ROLES_PERMS_MAX], int m, int n, int *res) {
  int i, j;
  for(i=0;i<m;i++) {
    fprintf(fp,"%s [ %s ] :",keyword,xname[i]);
    for(j=0;j<n;j++) {
      int tmp=r2a_aux(r[i][j]);
      /* printf("r2a_aux(r[%d][%d])=%d\n",i,j,tmp); */
      if(res && r[i][j]>=0 && res[tmp-1]>0)
	fprintf(fp," %s",yname[j]);
    }
    fprintf(fp," ;\n");
  }
}

void print_attributes(FILE *fp,char const keyword[], char *xname[], char *yname[], int r[], int m, int n) {
  int i;
  for(i=0;i<m;i++) {
    fprintf(fp,"%s [ %s ] : %s ;\n",keyword,xname[i],yname[r[i]]);
  }
}

void print_mer(FILE *fp, mer_type mer) {
  int j;
  fprintf(fp,"mer %s %s %d ",sscope_name[mer.sscope],tscope_name[mer.tscope],mer.n);
  for(j=0;j<mer.rs_card;j++)
    fprintf(fp,"%s ",rname[mer.rs[j]]);
  fprintf(fp,";\n");
}

void print_mers(FILE *fp, mer_type mer[], int num_mers) {
  int i;
  for(i=0;i<num_mers;i++)
    print_mer(fp,mer[i]);
}

int *select_aux(sscope_type sscope, tscope_type tscope) {
  if(sscope==ms && tscope==d)
    return msd_aux;
  if(sscope==ss && tscope==h)
    return ssh_aux;
  if(sscope==ms && tscope==h)
    return msh_aux;
  fprintf(stderr,"Logical error in select_aux: this statement should not be reachable.\n");
  exit(EXIT_FAILURE);
}

int read_mers() {
  char token[60];
  int r;
  for(r=0;r<ROLES_MAX;r++) {
    msd_aux[r]=-1;
    ssh_aux[r]=-1;
    msh_aux[r]=-1;
  }
  fscanf(fp_spec,"%s",token);
  while(strcmp(token,"mer")==0) {
    fscanf(fp_spec,"%s",token);
    if(strcmp(token,"ss")==0)
      mer[num_mers].sscope=ss;
    else {
      if(strcmp(token,"ms")==0)
	mer[num_mers].sscope=ms;
      else {
	fprintf(stderr,"Syntax error in reading_mers: expected 'ss' or 'ms', found %s.\n", token);
	exit(EXIT_FAILURE);
      }
    }
    fscanf(fp_spec,"%s",token);
    if(strcmp(token,"d")==0)
      mer[num_mers].tscope=d;
    else {
      if(strcmp(token,"h")==0)
	mer[num_mers].tscope=h;
      else {
	fprintf(stderr,"Syntax error in reading_mers: expected 'd' or 'h', found %s.\n", token);
	exit(EXIT_FAILURE);
      }
    }
    if(fscanf(fp_spec,"%d",&(mer[num_mers].n))!=1) {
      fprintf(stderr,"Syntax error in reading_mers: expected number, found something else.\n");
      exit(EXIT_FAILURE);
    }
    fscanf(fp_spec,"%s",token);
  /* printf("reading role=%s, strcmp=%d\n",token,strcmp(token,";")); */
    mer[num_mers].rs_card=0;
    while(strcmp(token,";")!=0) {
    /* printf("reading identifier=%s\n",token); */
      int j;
    for(j=0;(j<num_roles && strcmp(rname[j],token)!=0);j++);
    if(j==num_roles) {
      fprintf(stderr,"reading_mers: Identifier %s not declared.\n", token);
      exit(EXIT_FAILURE);
    }
    mer[num_mers].rs[mer[num_mers].rs_card]=j;
    if(mer[num_mers].sscope!=ss||mer[num_mers].tscope!=d) {
      int *aux;
      aux=select_aux(mer[num_mers].sscope,mer[num_mers].tscope);
      if(aux[j]<0)
	aux[j]=num_aux++;
    }
    mer[num_mers].rs_card++;
    fscanf(fp_spec,"%s",token);
    }
    num_mers++;
    fscanf(fp_spec,"%s",token);
  }
  return(num_mers-1);
}

FILE *cc(int n, int rs_card, int i) {
  int nv, nc;
  FILE *fp;
  char cmd[2000], token[60], tmp[200];
  char tmpfile[PATH_MAX+1], cmdfile[PATH_MAX+1], errfile[PATH_MAX+1];
  strip_prefix(tmp,bname);
  sprintf(tmpfile,"%s-cc%d.dimacs",tmp,i);
  /* printf("tmpfile=%s\n",tmp); */
  sprintf(errfile,"%s-cc%d.err",tmp,i);
  /* printf("errfile=%s\n",tmp); */
  sprintf(cmdfile,"%s-cc%d.cmd",tmp,i);
  sprintf(cmd,"%s/ParCounter %d %d > %s 2> %s",ccpath,n,rs_card,tmpfile,errfile);
  /* printf("cmdfile=%s, errfile=%s, cmd=%s\n",cmdfile,errfile,cmd); */
  fp = fopen(cmdfile,"w");
  fprintf(fp,"%s\n",cmd);
  fclose(fp);
  system(cmd);
  fp = fopen(tmpfile, "r");
  if (fp == NULL) {
    fprintf(stderr, "Can't open input tmpfile!\n");
    exit(EXIT_FAILURE);
  }
  char c;
  while ((c=fgetc(fp))=='c') {
    /* putchar(c); */
    while((c=fgetc(fp))!='\n') {
      /* putchar(c); */
    }
  }
  ungetc(c,fp);
  fflush(stdout);
  fscanf(fp,"%s %s %d %d",token,tmp,&nv,&nc);
  /* printf("nv=%d nc=%d\n",nv,nc); */
  if(strcmp(token,"p")!=0)  {
    fprintf(stderr,"Syntax error in dimacs file: line 'p cnf nc nv' expected.  Found '%s' in file %s!\n",token,tmpfile);
  }
  return fp;
}

void print_role_symbolic(char s, int n) {
  if(s=='-') {
    printf("-");
  }
  printf("%s ",rname[n]);
}

void print_role(FILE *fp, char s, int n) {
  if(s=='-') {
    fprintf(fp,"-");
    #ifdef DEBUG
      fprintf(fp_debug,"-");
    #endif
  }
  fprintf(fp,"%d ",r2a_role(n));
  #ifdef DEBUG
    fprintf(fp_debug,"%s ",rname[n]);
  #endif
}

void print_perm_symbolic(char s, int n) {
  if(s=='-') {
    printf("-");
  }
  printf("%s ",pname[n]);
}

void print_perm(FILE *fp, char s, int n) {
  if(s=='-') {
    fprintf(fp,"-");
    #ifdef DEBUG
      fprintf(fp_debug,"-");
    #endif
  }
  fprintf(fp,"%d ",r2a_perm(n));
  #ifdef DEBUG
    fprintf(fp_debug,"%s ",pname[n]);
  #endif
}

void print_aux(FILE *fp, char sign, int n) {
  if(sign=='-') {
    fprintf(fp,"-");
    #ifdef DEBUG
      fprintf(fp_debug,"-");
    #endif
  }
  fprintf(fp,"%d ",r2a_aux(n));
  #ifdef DEBUG
    int s, r;
    for(s=0;s<num_sesss;s++) {
      for(r=0;r<num_roles;r++) {
	/* fprintf(fp_debug,"%d ",once_aux[s][r]); */
	/* fprintf(fp_debug,"s=%d, r=%d, n=%d, yesterday_aux[%d][%d]=%d\n",s,r,n,s,r,yesterday_aux[s][r]); */
	if(n==yesterday_aux[s][r]) {
	  fprintf(fp_debug,"Y[%d][%d] ",s,r);
	  return;
	}
	if(n==once_aux[s][r]) {
	  fprintf(fp_debug,"O[%d][%d] ",s,r);
	  /* fprintf(fp_debug,"O%d[%d][%d] ",n,s,r); */
	  return;
	}
      }
      /* fprintf(fp_debug,"\n"); */
    }
    fprintf(fp_debug,"aux%d ",n);
  #endif
}

void print_eoc(FILE *fp) {
    fprintf(fp,"0\n");
    #ifdef DEBUG
      fprintf(fp_debug,"0\n");
    #endif
    num_clauses++;
}

int check_unsat(char dimacsfile[]) {
  char dimacsfile0[PATH_MAX+1];
  char buf[10000];
  int nv, nc, top;
  /* printf("I am here!\n"); */
  strcpy(dimacsfile0,dimacsfile);
  strcat(dimacsfile0,"0");
  FILE *fpin, *fpout;
  fpin = fopen(dimacsfile, "r");
  fpout = fopen(dimacsfile0, "w");
  /* printf("I am here 1!\n"); */
  while(fgets(buf,10000,fpin)!=NULL && buf[0]=='c');
  sscanf(buf,"p wcnf %d %d %d",&nv,&nc,&top);
  fprintf(fpout,"p cnf %d %d\n",nv,nc);
  /* printf("I am here 2!\n"); */
  while(fgets(buf,10000,fpin)!=NULL) {
    int i, w;
    /* printf("I am here 3! buf=%s\n",buf); */
    w=0;
    for(i=0;buf[i]>='0'&&buf[i]<='9';i++)
      w=10*w+buf[i]-'0';
    /* printf("I am here 4! top=%d w=%d\n",top,w); */
    if(w==top)
      fprintf(fpout,"%s",buf+i+1);
  }
  fclose(fpin);
  fclose(fpout);
  strip_prefix(resfile,dimacsfile); strcat(resfile,".res-minisat");
  strip_prefix(errfile,specfile); strcat(errfile,".err-minisat");
  sprintf(buf,"%s/minisat.exe %s > %s 2> %s",satsolverpath,dimacsfile0,resfile,errfile);
  system(buf);
  /* fprintf(stderr, "***%s***\n",buf); */
  fpin = fopen(resfile,"r");
  if (fpin == NULL) {
    fprintf(stderr, "Can't open input %s!\n",resfile);
    exit(EXIT_FAILURE);
  }
  while(fgets(buf,10000,fpin)!=NULL);
  /* printf("buf=%s, cmp=%d\n",buf,strncmp(buf,"UNSATISFIABLE",13)); */
  if(strncmp(buf,"UNSATISFIABLE",13)==0)
    return 1;
  else {
    /* printf("Why am I here?\n"); */
    return 0;
  }
}

int *solve() {
  char buf[1000], resfile[PATH_MAX+1], errfile[PATH_MAX+1];
  FILE *fp;
  strip_prefix(resfile,specfile); strcat(resfile,".res");
  strip_prefix(errfile,specfile); strcat(errfile,".err");
  if(GENERATE>0 && check_unsat(dimacsfile))
    return NULL;
  sprintf(buf,"%s %s > %s 2> %s",SATSolverCmdString,dimacsfile,resfile,errfile);
  system(buf);
  fprintf(stderr, "***%s***\n",buf);
  fp = fopen(resfile, "r");
  if (fp == NULL) {
    fprintf(stderr, "Can't open input %s!\n",resfile);
    exit(EXIT_FAILURE);
  }
  printf("Parsing %s\n",resfile);
  char c;
  while ((c=fgetc(fp))!='v' && c!=EOF) {
    while((c=fgetc(fp))!='\n');
  }
  if(c==EOF)
    return NULL;
  int *model=new int[num_roles+num_perms+num_aux];
  int sign, val, nread;
  printf("Reading model...\n");
  sign=1; val=0; nread=0;
  fgetc(fp);
  while ((c=fgetc(fp))!=EOF) {
    /* printf("val=%d, c=%c\n",val,c); */
    if(c=='-') {
      sign=-1;
      continue;
    }
    if(c>='0' && c<='9') {
      val=10*val+c-'0';
      nread=1;
      if(val==0)
	break;
      continue;
    }
    if(nread==1 && (c==' '||c=='\t'||c=='\n'||c=='v')) {
      /* fprintf(stderr,"model[%d]=%d\n",val-1,sign); */
      model[val-1]=sign;
      sign=1; val=0;
      nread=0;
      continue;
    }
    /* fprintf(stderr,"model[%d]=%d\n",model[val],sign); */
    /* model[val]=sign; */
    break;
  }
  return model;
}

void encode() {
  int r, p, s;
  char token[60];
  for(p=0;p<PERMS_MAX;p++)
    grant[p]=deny[p]=0;
  read_entities("users",uname,num_users);
  read_entities("roles",rname,num_roles);
  read_entities("perms",pname,num_perms);
  read_entities("sesss",sname,num_sesss);
  read_attribute("sof",sname,uname,sof,num_sesss,num_users);
  //printf("UA RElations");
  read_relations("ua",uname,rname,ua,num_users,num_roles);
  //printf("PA RElations");
  read_relations("pa",rname,pname,pa,num_roles,num_perms);
  //printf("ERROR NOT SEE");
  read_yo("yesterday",sname,rname,yesterday_aux,num_sesss,num_roles);
  read_yo("once",sname,rname,once_aux,num_sesss,num_roles);

  char encfile[PATH_MAX+1];
  strip_prefix(encfile,bname);
  strcat(encfile,".enc");
  fp_enc=fopen(encfile,"w");

  #ifdef DEBUG
    fprintf(fp_debug,"--- Role => Perm\n");
  #endif
  for(r=0;r<num_roles;r++) {
    for(p=0;p<num_perms;p++)
      if(pa[r][p]==1) {
	print_role(fp_enc,'-',r);
	print_perm(fp_enc,'+',p);
	print_eoc(fp_enc);
      }
#ifdef WQL
    int at_least_one_perm;
    at_least_one_perm=0;
    for(p=0;p<num_perms;p++)
      if(pa[r][p]==1) {
	print_perm(fp_enc,'-',p);
	at_least_one_perm=1;
      }
    if(at_least_one_perm) {
      print_role(fp_enc,'+',r);
      print_eoc(fp_enc);
    }
#endif
  }
  #ifdef DEBUG
    fprintf(fp_debug,"--- Perm => \\/ Roles\n");
  #endif
  for(p=0;p<num_perms;p++) {
    print_perm(fp_enc,'-',p);
    for(r=0;r<num_roles;r++)
      if(pa[r][p]==1)
	print_role(fp_enc,'+',r);
    print_eoc(fp_enc);
  }
  if(GENERATE>0) {
    #ifdef DEBUG
      fprintf(fp_debug,"--- yesterday implies once\n");
    #endif
    for(s=0;s<num_sesss;s++)
      for(r=0;r<num_roles;r++) {
	print_aux(fp_enc,'-',aux_for_yesterday(s,r));
	print_aux(fp_enc,'+',aux_for_once(s,r));
	print_eoc(fp_enc);
      }
  }
  else {
    #ifdef DEBUG
      fprintf(fp_debug,"--- yesterday and once\n");
    #endif
    for(s=0;s<num_sesss;s++)
      for(r=0;r<num_roles;r++) {
	if(once_aux[s][r]>=0) {
	  print_aux(fp_enc,'+',aux_for_once(s,r));
	  print_eoc(fp_enc);
	}
	else {
	  print_aux(fp_enc,'-',aux_for_once(s,r));
	  print_eoc(fp_enc);
	}
	if(yesterday_aux[s][r]>=0) {
	  print_aux(fp_enc,'+',aux_for_yesterday(s,r));
	  print_eoc(fp_enc);
	}
	else {
	  print_aux(fp_enc,'-',aux_for_yesterday(s,r));
	  print_eoc(fp_enc);
	}
      }
  }
  #ifdef DEBUG
      fprintf(fp_debug,"--- -ua => -r\n");
  #endif
  for(r=0;r<num_roles;r++) {
    /* printf("ua[sof[%d]][%d]=%d\n",s,r,ua[sof[s]][r]); */
    if(ua[sof[sid]][r]==0) {
      print_role(fp_enc,'-',r);
      print_eoc(fp_enc);
    }
  }
  // processing mer constraints
  read_mers();
  /* printf("ssh_aux :"); */
  /* for(r=0;r<num_roles;r++) */
  /*   printf(" %d",ssh_aux[r]); */
  /* printf("\n"); */
  /* printf("------------------------------------------------------\n"); */
  int i, j;
  for(i=0;i<num_mers;i++) {
    #ifdef DEBUG
      fprintf(fp_debug,"--- mer %s %s %d ",sscope_name[mer[i].sscope],tscope_name[mer[i].tscope],mer[i].n);
      for(j=0;j<mer[i].rs_card;j++)
	fprintf(fp_debug,"%s ",rname[mer[i].rs[j]]);
      fprintf(fp_debug,";\n");
    #endif
    int l;
    #ifdef SMART_MER_ENCODING
    int nlx=0;
    FILE *fpcc;
    fpcc=cc(mer[i].n-1,mer[i].rs_card,i);
    while(fscanf(fpcc,"%d",&l)==1) {
      while(l!=0) {
	int al;
	al=abs(l);
	nlx=MAX(al-mer[i].rs_card,nlx);
	if(al>0 && al<=mer[i].rs_card) {
	  if(mer[i].sscope==ss&&mer[i].tscope==d)
	    print_role(fp_enc,sign(l),mer[i].rs[al-1]);
	  else {
	    int *aux;
	    aux=select_aux(mer[i].sscope,mer[i].tscope);
	    print_aux(fp_enc,sign(l),aux[mer[i].rs[al-1]]);
	  }
	}
	else {
	  print_aux(fp_enc,sign(l),num_aux+al-mer[i].rs_card-1);
	}
	fscanf(fpcc,"%d ",&l);
      }
      print_eoc(fp_enc);
    }
    num_aux+=nlx;
    #else
    int x, y, z;
    int M=mer[i].n;
    /* printf("M=%d\n",M); */
    int N=mer[i].rs_card;
    /* printf("N=%d\n",N); */
    int *p=new int[N+2];
    int *b=new int[N];
    inittwiddle(M,N,p);
    for(j=0;j!=N-M;j++)
      b[j]=0;
    for(;j!=N;j++)
      b[j]=1;
    int more;
    do {
      /* for(j=0;j<N;j++) */
      /* 	putchar(b[j]? '1': '0'); */
      /* putchar('\n'); */
      /* printf("x=%d\n",x); */
      /* printf("y=%d\n",y); */
      /* fflush(stdout); */
      l=0;
      while (1) {
	for(;l<N&&b[l]==0;l++);
	/* printf("l=%d\n",l); */
	if(l==N)
	  break;
	if(mer[i].sscope==ss&&mer[i].tscope==d) {
	  print_role(fp_enc,'-',mer[i].rs[l]);
	  /* printf("mer[%d].rs[%d]=%d\n",i,l,mer[i].rs[l]); */
	}
	else {
	  int *aux;
	  aux=select_aux(mer[i].sscope,mer[i].tscope);
	  print_aux(fp_enc,'-',aux[mer[i].rs[l]]);
	}
	l++;
      }
      print_eoc(fp_enc);
      more=twiddle(&x, &y, &z, p);
      /* printf("hello! dopo twiddle\n"); */
      b[x]=1;
      b[y]=0;
    } while(!more);
    delete[] p;
    delete[] b;
    #endif
  }
  /* printf("num_aux=%d\n",num_aux); */
    #ifdef DEBUG
      fprintf(fp_debug,"--- mer aux\n");
    #endif
  for(i=0;i<num_roles;i++) {
    /* printf("r=%d ssh_aux=%d msd_aux=%d msh_aux=%d\n",i,ssh_aux[i],msd_aux[i],msh_aux[i]); */
    if(ssh_aux[i]>=0) {
      print_aux(fp_enc,'-',ssh_aux[i]);
      print_role(fp_enc,'+',i);
      print_aux(fp_enc,'+',aux_for_once(sid,i));
      print_eoc(fp_enc);
      print_role(fp_enc,'-',i);
      print_aux(fp_enc,'+',ssh_aux[i]);
      print_eoc(fp_enc);
      print_aux(fp_enc,'-',aux_for_once(sid,i));
      print_aux(fp_enc,'+',ssh_aux[i]);
      print_eoc(fp_enc);
    }
    if(msd_aux[i]>=0) {
      int s1;
      print_aux(fp_enc,'-',msd_aux[i]);
      print_role(fp_enc,'+',i);
      for(s1=0;s1<num_sesss;s1++)
	if(s1!=sid&&sof[s1]==sof[sid])
	  print_aux(fp_enc,'+',aux_for_yesterday(s1,i));
      print_eoc(fp_enc);
      print_role(fp_enc,'-',i);
      print_aux(fp_enc,'+',msd_aux[i]);
      print_eoc(fp_enc);
      for(s1=0;s1<num_sesss;s1++)
	if(s1!=sid&&sof[s1]==sof[sid]) {
	  print_aux(fp_enc,'-',aux_for_yesterday(s1,i));
	  print_aux(fp_enc,'+',msd_aux[i]);
	  print_eoc(fp_enc);
	}
    }
    if(msh_aux[i]>=0) {
      int s1;
      print_aux(fp_enc,'-',msh_aux[i]);
      print_role(fp_enc,'+',i);
      for(s1=0;s1<num_sesss;s1++) {
	/* fprintf(fp_debug,"s=%d s1=%d\n",sid,s1); */
	if(sof[s1]==sof[sid]) {
	  int afo;
	  afo=aux_for_once(s1,i);
	  /* fprintf(fp_debug,"afo[%d][%d]=%d ",s1,i,afo); */
	  print_aux(fp_enc,'+',afo);
	}
      }
      print_eoc(fp_enc);
      print_role(fp_enc,'-',i);
      print_aux(fp_enc,'+',msh_aux[i]);
      print_eoc(fp_enc);
      for(s1=0;s1<num_sesss;s1++)
	if(sof[s1]==sof[sid]) {
	  print_aux(fp_enc,'-',aux_for_once(s1,i));
	  print_aux(fp_enc,'+',msh_aux[i]);
	  print_eoc(fp_enc);
	}
    }
  }
  // processing the query
  fscant(fp_spec,"QUERY");
  fscanf(fp_spec,"%s",token);
  for(sid=0;sid<num_sesss&&strcmp(token,sname[sid])!=0;sid++);
  if(sid==num_sesss) {
    fprintf(stderr,"Syntax error in query: expected %s, found %s.\n","session id",token);
    exit(EXIT_FAILURE);
  }
  /* printf("sid=%d\n",sid); */
    #ifdef DEBUG
    fprintf(fp_debug,"--- query\n");
    #endif
  fscanf(fp_spec,"%s",token);
  if(strcmp(token,"ANY")==0) {
     OBJ=any;
  }
  else { 
    if(strcmp(token,"MIN")==0) {
      OBJ=min;
    }
    else { 
      if(strcmp(token,"MAX")==0) {
	OBJ=max;
      }
      else {
	fprintf(stderr,"Syntax error in query: expected ANY, MIN or MAX, found %s.\n",token);
	exit(EXIT_FAILURE);
      }
    }
  }
  fscant(fp_spec,"GRANT");
  fscanf(fp_spec,"%s",token);
  /* printf("reading role=%s, strcmp=%d\n",token,strcmp(token,";")); */
  while(strcmp(token,"DENY")!=0) {
    int i;
    /* printf("reading identifier=%s\n",token); */
    for(i=0;(i<num_perms&&(strcmp(pname[i],token)!=0));i++);
    if(i==num_perms) {
      fprintf(stderr,"Error in query: expected a permission, found '%s'.\n",token);
      exit(EXIT_FAILURE);
    }
    grant[i]=1;
    /* print_perm(fp_enc,'+',i); */
    /* print_eoc(fp_enc); */
  fscanf(fp_spec,"%s",token);
  }
  fscanf(fp_spec,"%s",token); // parsing next token after "DENY"
  /* printf("reading role=%s, strcmp=%d\n",token,strcmp(token,";")); */
    /* printf("deny[] = "); */
  while(strcmp(token,";")!=0) {
    int i;
    /* printf("reading identifier=%s\n",token); */
    for(i=0;(i<num_perms&&(strcmp(pname[i],token)!=0));i++);
    if(i==num_perms) {
      fprintf(stderr,"Error in query: expected a permission, found '%s'.\n",token);
      exit(EXIT_FAILURE);
    }
    deny[i]=1;
    /* printf("%d ",i); */
    fscanf(fp_spec,"%s",token);
  }
  /* printf("\n"); */
  fclose(fp_enc);
  
  // adding preamble to get proper dimacs format
  int l, EOC, top;
  strip_prefix(dimacsfile,bname);
  strcat(dimacsfile,".dimacs");
  FILE *fp_dimacs = fopen(dimacsfile,"w");
  top=num_clauses+num_perms;
  /* for(p=0;p<num_perms;p++) { */
  /*   if(deny[p]==1) { */
  /*     top++; */
  /*     continue; */
  /*   } */
  /*   if(grant[p]==0) */
  /*     top++; */
  /* } */
  if(GENERATE>0)
    top+=2*num_sesss*num_roles;
  fprintf(fp_dimacs,"p wcnf %d %d %d\n",num_roles+num_perms+num_aux,top,top);
  fp_enc=fopen(encfile,"r");
  EOC=1;
  while(fscanf(fp_enc,"%d",&l)>0) {
    if (EOC==1) {
      fprintf(fp_dimacs,"%d ",top);
      EOC=0;
    }
    fprintf(fp_dimacs,"%d ",l);
    if(l==0) {
      EOC=1;
      fprintf(fp_dimacs,"\n");
    }
  }
  for(p=0;p<num_perms;p++) { 
    if(grant[p]==1) { 
      fprintf(fp_dimacs,"%d ",top);
      print_perm(fp_dimacs,'+',p);
      print_eoc(fp_dimacs);
    }
    else if(deny[p]==1) {
      fprintf(fp_dimacs,"%d ",top);
      print_perm(fp_dimacs,'-',p);
      print_eoc(fp_dimacs);
    }
    else {  // not deny AND not grant
      if(GENERATE>0) {
	fprintf(fp_dimacs,"1 ");
	print_perm(fp_dimacs,'-',p);
	print_eoc(fp_dimacs);
      }
      else {
	if(OBJ==max) {
	  fprintf(fp_dimacs,"1 ");
	  print_perm(fp_dimacs,'+',p);
	  print_eoc(fp_dimacs);
	}
	if(OBJ==min) {
	  fprintf(fp_dimacs,"1 ");
	  print_perm(fp_dimacs,'-',p);
	  print_eoc(fp_dimacs);
	}
      }
    }
  }
  if(GENERATE>0) {
    #ifdef DEBUG
      fprintf(fp_debug,"--- promote yesterday and once during generation\n");
    #endif
    for(s=0;s<num_sesss;s++)
      for(r=0;r<num_roles;r++) {
	/* fprintf(fp_dimacs,"%d ",MAX(1,(1*top)/8)); */
	fprintf(fp_dimacs,"%d ",1);
	print_aux(fp_dimacs,((r%2)?'+':'-'),aux_for_yesterday(s,r));
	print_eoc(fp_dimacs);
	/* fprintf(fp_dimacs,"%d ",MAX(1,(1*top)/8)); */
	fprintf(fp_dimacs,"%d ",1);
	print_aux(fp_dimacs,((r%2)?'+':'-'),aux_for_once(s,r));
	print_eoc(fp_dimacs);
	/* printf("num_clauses=%d\n",num_clauses); */
      }
  }
  /* if(top!=num_clauses) { */
  /*   fprintf(stderr,"Error in encoding: top(%d)!=num_clauses(%d).\n",top, num_clauses); */
  /*   exit(EXIT_FAILURE); */
  /*   } */
  fclose(fp_dimacs);
  fclose(fp_enc);
}

void print_result(const int res[]) { 
  if(res==NULL) {
    fprintf(stdout,"NO SOLUTION\n");
    #ifdef DEBUG
      fprintf(fp_debug,"--- no solution\n");
    #endif
    return;
  }
  printf("SOLUTION: ");
    #ifdef DEBUG
      fprintf(fp_debug,"--- solution\n");
    #endif
  int al;
  for(al=0;al<num_roles+num_perms+num_aux;al++) {
    if(rolep(al)) {
      print_role(stdout,sign(res[al]),a2r_role(al+1));
      continue;
    }
    if(permp(al)) {
      print_perm(stdout,sign(res[al]),a2r_perm(al+1));
      continue;
    }
    if(auxp(al)) {
      print_aux(stdout,sign(res[al]),a2r_aux(al+1));
    }
  }
  printf("\n");
  printf("ANSWER: ");
  for(al=0;al<num_roles+num_perms+num_aux;al++) {
    if(rolep(al)) {
      print_role_symbolic(sign(res[al]),a2r_role(al+1));
      continue;
    }
    if(permp(al)) {
      print_perm_symbolic(sign(res[al]),a2r_perm(al+1));
    }
  }
  printf("\n");

  char tmpfn[PATH_MAX+1], yfn[PATH_MAX+1], ofn[PATH_MAX+1];
  strip_prefix(tmpfn,bname);
  sprintf(yfn,"%s.yesterday",tmpfn);
  sprintf(ofn,"%s.once",tmpfn);
  FILE *yfp, *ofp;
  yfp=fopen(yfn,"w");
  ofp=fopen(ofn,"w");

  int i, j;
  for(i=0;i<num_sesss;i++) {
    fprintf(yfp,"%s : ",sname[i]);
    fprintf(ofp,"%s : ",sname[i]);
    for(j=0;j<num_roles;j++) {
      /* printf("yesterday_aux[%d][%d]=%d res[..]=%d\n",i,j,r2a_aux(yesterday_aux[i][j]),res[r2a_aux(yesterday_aux[i][j])-1]); */
      /* printf("once_aux[%d][%d]=%d res[..]=%d\n",i,j,r2a_aux(once_aux[i][j]),res[r2a_aux(once_aux[i][j])-1]); */
      if(yesterday_aux[i][j]>=0 && res[r2a_aux(yesterday_aux[i][j])-1]>0)
	fprintf(yfp,"%s ",rname[j]);
      if(once_aux[i][j]>=0 && res[r2a_aux(once_aux[i][j])-1]>0)
	fprintf(ofp,"%s ",rname[j]);
    }
    fprintf(yfp,";\n");
    fprintf(ofp,";\n");
  }
  fclose(yfp);
  fclose(ofp);
}

void print_uaq(int *res, char ofilename[]) {
  FILE *fp;
  int i;
  char sf[PATH_MAX+1];
  strip_prefix(sf,ofilename);
  sprintf(newspecfile,"%s.uaq",sf);
  fp = fopen(newspecfile,"w");
  print_entities(fp,"users",uname,num_users);
  print_entities(fp,"roles",rname,num_roles);
  print_entities(fp,"perms",pname,num_perms);
  print_entities(fp,"sesss",sname,num_sesss);
  fprintf(fp,"\n");
  print_attributes(fp,"sof",sname,uname,sof,num_sesss,num_users);
  fprintf(fp,"--\n");
  print_relations(fp,"ua",uname,rname,ua,num_users,num_roles);
  fprintf(fp,"--\n");
  print_relations(fp,"pa",rname,pname,pa,num_roles,num_perms);
  fprintf(fp,"--\n");
  print_yo(fp,"yesterday",sname,rname,yesterday_aux,num_sesss,num_roles,res);
  fprintf(fp,"--\n");
  print_yo(fp,"once",sname,rname,once_aux,num_sesss,num_roles,res);
  fprintf(fp,"--\n");
  print_mers(fp,mer,num_mers);
  fprintf(fp,"--\n");
  fprintf(fp,"QUERY %s %s GRANT ",sname[sid],(OBJ==any?"ANY":(OBJ==min?"MIN":(OBJ==max?"MAX":"ERROR"))));
  for(i=0;i<num_perms;i++)
    if(grant[i]==1)
      fprintf(fp,"%s ",pname[i]);
  /* fprintf(fp,"DENY ",sname[sid]); */
  fprintf(fp,"DENY ");
  if(GENERATE>0) {
    if(res) {
      int j; j=NUM_SLACK_VARS;
      for(i=0;i<num_perms;i++)
      /* printf(">>>>i=%d r2a_perm(i)=%d, res[r2a_perm(i)-1]=%d<<<<\n",i,r2a_perm(i),res[r2a_perm(i)-1]); */
      /* printf(">>>>i=%d r2a_perm(i)=%d<<<<\n",i,r2a_perm(i)); */
	if(res[r2a_perm(i)-1]<0)
	  if(j>0)
	    j--;
	  else {
	    fprintf(fp,"%s ",pname[i]);
	  }
    }
  }
  else {
    for(i=0;i<num_perms;i++)
      if(deny[i]==1)
	fprintf(fp,"%s ",pname[i]);
  }
  fprintf(fp,";\n");
  fclose(fp);
}

void print_usage(char cmd[]) {
  printf("Usage: %s [-g|--generate] -v num_slack_vars -o|--output filename --satsolver SATSolver\n",cmd);
}

int main(int argc, char *argv[]) {
  int opt= 0;
  char ofilename[150], SATSolver[50];
  ccpath=getenv("CCPATH");
  satsolverpath=getenv("SATSOLVERPATH");

  GENERATE=0;
  static struct option long_options[] = {
    {"generate",  no_argument,              0,  'g' },
    {"slack-vars",  required_argument,      0,  'v' },
    {"output",  required_argument,          0,  'o' },
    {"satsolver",  required_argument,       0,  's'},
    {0,           0,                        0,  0   }
  };

  int long_index =0;
  while ((opt = getopt_long(argc, argv,"gv:o:s:", long_options, &long_index )) != -1) {
    switch (opt) {
    case 'g' : GENERATE = 1;
      break;
    case 'v' : NUM_SLACK_VARS=atoi(optarg);
      break;
    case 'o' : strcpy(ofilename,optarg);
      break;
    case 's' : strcpy(SATSolver,optarg);
      break;
    default: print_usage(argv[0]); 
      exit(EXIT_FAILURE);
    }
  }

  printf("satsolver = %s\n",SATSolver);
  
  if(GENERATE) { 
    if(strcmp(SATSolver,"qmaxsat")==0)
      sprintf(SATSolverCmdString,"%s/qmaxsat14.04auto-glucose3_static",satsolverpath);
    else {
      if (strcmp(SATSolver,"CCLS2014-Bounded")==0)
	sprintf(SATSolverCmdString,"%s/CCLS2014-Bounded.exe",satsolverpath);
      else {
	if (strcmp(SATSolver,"CCLS_to_akmaxsat")==0)
	  sprintf(SATSolverCmdString,"%s/CCLS_to_akmaxsat.exe",satsolverpath);
	else {
	  if (strcmp(SATSolver,"WPM1")==0)
	    sprintf(SATSolverCmdString,"%s/WPM1-2012",satsolverpath);
	  else {
            if (strcmp(SATSolver,"Loandra")==0)
               sprintf(SATSolverCmdString,"%s/loandra_static -no-incremental -algorithm=7",satsolverpath);
            else {
	      printf("Error: SAT solver set to '%s'.\nCurrently supported weighted Max SAT solvers for *generating* UAQ Problems are: qmaxsat and CCLS_to_akmaxsat.\n",SATSolver);
	      exit(EXIT_FAILURE);
            }
	  }
	}
      }
    }
  }
  else {
    if(strcmp(SATSolver,"qmaxsat")==0)
      sprintf(SATSolverCmdString,"%s/qmaxsat14.04auto-glucose3_static",satsolverpath);
    else {
      if (strcmp(SATSolver,"sat4j")==0)
	sprintf(SATSolverCmdString,"/usr/bin/java -jar %s/sat4j-maxsat.jar",satsolverpath);
      else {
	if (strcmp(SATSolver,"maxsatz")==0)
	  sprintf(SATSolverCmdString,"%s/maxsatz2013f",satsolverpath);
	else {
	     if (strcmp(SATSolver,"WPM1")==0)
	       sprintf(SATSolverCmdString,"%s/WPM1-2012",satsolverpath);
	       /* sprintf(SATSolverCmdString,"%s/wpm2014.in",satsolverpath); */
	     else {
		if (strcmp(SATSolver, "maxino") == 0)
	           sprintf(SATSolverCmdString,"%s/maxino-2015-kdyn", satsolverpath);
		else{
                   if (strcmp(SATSolver,"Loandra")==0)
                     sprintf(SATSolverCmdString,"%s/loandra_static -no-incremental -algorithm=7",satsolverpath);
                   else{
	             printf("Error: SAT solver set to '%s'.\nCurrently supported partial Max SAT solvers for *solving* UAQ Problems are: qmaxsat, sat4j, maxsatz, and WPM1.\n",SATSolver);
	             exit(EXIT_FAILURE);
                   }
	     }
	  }
	}
      }
    }
  }

  char debugfile[PATH_MAX+1];
  int *res;
  realpath(argv[optind],specfile);
  fp_spec=fopen(specfile,"r");
  if(fp_spec==NULL) {
    fprintf(stderr,"Error: file %s does not exist.\n",specfile);
    exit(EXIT_FAILURE);
  }
  bname=basename(specfile);
  strip_prefix(debugfile,bname);
  strcat(debugfile,".debug");
  fp_debug = fopen(debugfile,"w");

  encode();

  if(strcmp(SATSolver,"")!=0) {
    res=solve();
    print_result(res);
  }

  if(GENERATE) {
    char *suffix;
    char pf[PATH_MAX+1];
    suffix=strip_prefix(pf,ofilename);
    strcat(pf,"-ANY");
    strcat(pf,suffix);
    OBJ=any;
    print_uaq(res,pf);
    suffix=strip_prefix(pf,ofilename);
    strcat(pf,"-MIN");
    strcat(pf,suffix);
    OBJ=min;
    print_uaq(res,pf);
    suffix=strip_prefix(pf,ofilename);
    strcat(pf,"-MAX");
    strcat(pf,suffix);
    OBJ=max;
    print_uaq(res,pf);
  }
  delete[] res;
  fclose(fp_spec);
  fclose(fp_debug);
  return 1;
}

  
