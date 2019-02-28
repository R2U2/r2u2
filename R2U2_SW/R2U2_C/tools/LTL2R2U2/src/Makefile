TARGET = r2u2prepare
#CPPFLAGS= $(INCLUDES:%=-I%) -DDEBUG
CPPFLAGS= $(INCLUDES:%=-I%)
CFLAGS= $(INCLUDES:%=-I%)
LDFLAGS = $(LIBRARIES:%=-L%)
INCLUDES	= ./

UNAME = ${shell uname}
ifeq ($(UNAME), Darwin)
LIBRARIES	= ./
LDLIBS	= -ll
endif
ifeq ($(UNAME), Linux)
LIBRARIES	= /opt/local/lib
LDLIBS	= -lfl
endif

MY_MODULES =\
	KItem\
	KList\
	main\
	lex.yy\
	y.tab\
	rtR2U2_util


MY_OBJS = $(MY_MODULES:%=%.o)
MY_SRC = $(MY_MODULES:%=%.c)

all: y.tab.c $(MY_OBJS)
	g++ -g ${CPPFLAGS} ${LDFLAGS} ${LDLIBS} ${OBJS} ${MY_OBJS} -o $(TARGET)


install: all
	mv $(TARGET) ../../bin

lex.yy.o: lex.yy.c
	g++ -g -c ${CPPFLAGS} lex.yy.c

lex.yy.c: lexrtR2U2.l
	lex lexrtR2U2.l

y.tab.c: yaccrtR2U2.y
	yacc -d yaccrtR2U2.y

y.tab.o: y.tab.c
	g++ -g -c ${CPPFLAGS} y.tab.c

clean:
	rm -f ./*.o lex.yy.c y.tab.c y.tab.h
