/************************************************************************/
/*                                                                      */
/*              ---------- ProQuel ----------                           */
/*                                                                      */
/* Version:     1.2               Language:       C                     */
/* Autor:       Michael Boehlen   System:         UNIX                  */
/* Created:     10. July 1991     Machine:        SUN                   */
/*                                                                      */
/* Module:      postgres_interface.c                                    */
/* Purpose:     C-Interface to Postgres                                 */
/* Export:      pg_open_db                                              */
/*              pg_close_db                                             */
/*              pg_exec                                                 */
/*              pg_get_col                                              */
/* Comment:     This is an adapted version of the file 'sql_inter.c'    */
/*              At runtime the following library must be present:      */
/*                /home/mint/postgres/obj.sunos4/libpq.a                */
/*                                                                      */
/* Modifications:       Name            Date            Sign            */
/*                                                                      */
/************************************************************************/

#include "/home/mint/postgres/src/lib/H/tmp/libpq.h"
#include <stdio.h>

extern char *PQexec();

static char* dummy = "dummy";

void pg_open_db(dbName)
  char* dbName;
{
  PQsetdb(dbName);
}

void pg_close_db()
{
  PQfinish();
}

void pg_exec(Stmt)
  char* Stmt;
{
  char* status;

  status = PQexec(Stmt);
}

void pg_get_buf(pg_buf)
  PortalBuffer **pg_buf;
{
  *pg_buf=PQparray("blank");
}

void pg_count_tuples(pg_buf,count)
  PortalBuffer *pg_buf;
  int *count;
{
  *count=PQntuples(pg_buf);
}

void pg_get_val(pg_buf,tupNr,colNr,value)
  PortalBuffer *pg_buf;
  int tupNr;
  int colNr;
  char **value;
{
  *value=PQgetvalue(pg_buf,tupNr,colNr);
}


/*
cc -I/home/mint/postgres/src/lib/H -c -o postgres_interface.o postgres_interface.c
*/
