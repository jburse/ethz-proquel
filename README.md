# What is this?

This repository contains Prolog texts of the ProQuel Deductive
Database System from 1991. There were separate versions depending
on the database target, including a plain Prolog target.

The Prolog texts were written for SICStus Prolog 0.x. The Prolog
texts contain also a linter and a cross referencer, this was used
to keep the code clean. But a module system wasn't used.

# ProQuel Source

The following Prolog text has been uploaded:
- [pro_quel/pro_flat_incore](https://github.com/jburse/ethz-proquel/tree/master/pro_quel/pro_flat_incore):
  ProQuel with plain Prolog target.
- [pro_quel/pro_flat_pg](https://github.com/jburse/ethz-proquel/tree/master/pro_quel/pro_flat_pg):
  ProQuel with plain Postgres target.
- [pro_quel/pro_flat_sql](https://github.com/jburse/ethz-proquel/tree/master/pro_quel/pro_flat_sql):
  ProQuel with plain Oracle target.

The "flat" in the directory name above means that this is the
Datalog version, where all predicate arguments are scalar datatypes.
We did not upload more advanced experimental versions that

were also pursued in the past.

# ProQuel Documentation

The following documents have been uploaded:
- [tex_dir/gelb](https://github.com/jburse/ethz-proquel/tree/master/tex_dir/gelb):
  Burse, J. (1992): ProQuel: Using Prolog to Implement a Deductive Database System

Jan Burse, 26.10.2019 (more testing)