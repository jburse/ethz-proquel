/************************************************************************/
/*									*/
/* 		---------- ProQuel ----------				*/
/*									*/
/* Version:	1.2		Language:	C			*/
/* Autor:	Jan Burse	System:		UNIX			*/
/* Created:	10. July 1991	Machine:	SUN			*/
/* 									*/
/* Module:	sql_inter.c						*/
/* Purpose:	C-Interface to Oracle/SQL				*/
/* Export:	sql_exec						*/
/* 		sql_open_cursor						*/
/*		sql_fetch_row						*/
/*		sql_get_column						*/
/*		sql_close_cursor					*/
/* Comment:	The whole information about Oracle/SQL calls comes	*/
/*		exclusively from the Oracle-manual:			*/
/*		  Donna Neville, "ORACLE: Pro*C User's Guide", 		*/
/*		  Version 1.1, Copyright 1987 Oracle Corporation,	*/
/*		  Belmont California, USA				*/
/*		At runtime the following libraries must be present:	*/
/*		  /home/mint/oracle/rdbms/lib/osntab.o			*/
/*		  /home/mint/oracle/c/lib/libocic.a			*/
/*		  /home/mint/oracle/rdbms/lib/libsqlnet.a		*/
/*		  /home/mint/oracle/rdbms/lib/libora.a			*/
/*		  /usr/5lib/libc.a					*/
/*									*/
/* Modifications:	Name		Date		Sign		*/
/*									*/
/************************************************************************/

#include <stdio.h>
#include <string.h>

extern olon();			/* open database */
extern ologof();		/* close database */
extern osql3();			/* compile statement */
extern oexec();			/* execute statement */
extern oopen();			/* open cursor */
extern oclose();		/* close cursor */
extern ofetch();		/* fetch row */
extern odsc();			/* get column desc */
extern odefin();		/* define column buffer */
extern ocan();			/* cancel fetch */
extern oermsg();		/* get error message */
extern ocon();			/* autocommit on */
extern obndrn();		/* bind numbered variable */

static char lda[64]; 		/* database workspace */

static perr(wp)
  char *wp;		/* IN: Workspace Pointer (lda or cda) */
{
  char msg[132];

  if (*wp!=0) {
    oermsg(*wp,msg);
    fputs(msg,stderr);
  };
}

typedef struct Sql_Fetch_Rec {
  int cols;			/* number of columns */
  char *bufs[32];		/* string buffers for the columns */
  char cda[64];			/* cursor workspace */
} *Sql_Fetch;

sql_open_cursor(s,p)
  char *s;		/* IN: SQL select statement */
  Sql_Fetch *p;		/* OUT: cursor */
{
  Sql_Fetch f;			

  f=(Sql_Fetch)malloc(sizeof(struct Sql_Fetch_Rec)); 	
  oopen(f->cda,lda,-1,-1,-1,-1,-1); 			
  perr(f->cda);
  osql3(f->cda,s,-1);					
  perr(f->cda);
  f->cols=-1;
  *p=f;
}

sql_put_variable(f,n,s)
  Sql_Fetch f;		/* IN: cursor */
  int n;		/* IN: variable */
  char *s;		/* IN: string */
{
  obndrn(f->cda,n,s,strlen(s),1);
  perr(f->cda);  
}

sql_fetch_row(f,d)
  Sql_Fetch f;		/* IN: cursor */
  int *d;		/* OUT: =0 row fetched, #0 no row fetched */
{
  int i;			/* counter for the output rows */
  short dsize;			/* local display size */
  short dbtype;			/* local type */

  if (f->cols==-1) {
    i=0;
    while (odsc(f->cda,i+1,0,0,0,&dbtype,0,0,&dsize)==0) {
      if (dbtype==8) dsize=1000;
      f->bufs[i]=(char*)malloc(dsize+1);				
      odefin(f->cda,i+1,f->bufs[i],dsize+1,5,-1,0,0,-1,-1,0,0); 	
      perr(f->cda);
      i++;
    };
    f->cols=i;
    oexec(f->cda);
    perr(f->cda);
  };
  *d=ofetch(f->cda);
}

sql_get_column(f,i,s)
  Sql_Fetch f;		/* IN: cursor */
  int i;		/* IN: column */
  char **s;		/* OUT: string */
{
  *s=f->bufs[i];
}

sql_exec_cursor(f)
  Sql_Fetch f;		/* IN: cursor */
{
  oexec(f->cda);
  perr(f->cda);
}

sql_close_cursor(f)
  Sql_Fetch f;		/* IN: cursor */
{
  int i;

  ocan(f->cda);
  perr(f->cda);
  oclose(f->cda);
  perr(f->cda);
  for (i=0; i<f->cols; i++) free(f->bufs[i]);
  free(f);
}

sql_open_db(s,d)
  char *s;
  int *d;
{
  olon(lda,s,-1,-1,-1,0);
  perr(lda);
  ocon(lda);
  perr(lda);
  *d=lda[0];
}

sql_close_db()
{
  ologof(lda);
  perr(lda);
}

/************************************************************************/
/* .									*/
/************************************************************************/
