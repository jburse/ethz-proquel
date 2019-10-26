CC_OPTION = -g

LIB_O = /home/mint/postgres/obj.sunos4/libpq.a

LIB_H = /home/mint/postgres/src/lib/H

postgres_interface: postgres_interface.o
  
.c.o:
	  cc $(CC_OPTION) -I$(LIB_H) -c $<

