

#define L_OPC	5
#define L_OP	10
#define L_INTVL	8
#define L_INTVL_TS	16
#define L_PMEM	7
#define L_TIMESTAMP	16


#define OP_START		"01011"
#define AOP_START		"re"
#define OP_END			"01100"
#define AOP_END			"fe"
#define OP_END_SEQUENCE		"11111"
#define AOP_END_SEQUENCE	"end"
#define OP_NOP			"11110"
#define AOP_NOP			"nop"

#define OP_NOT			"00011"
#define AOP_NOT			"not"
#define OP_AND			"00100"
#define AOP_AND			"and"
#define OP_IMPL			"00110"
#define AOP_IMPL		"impl"

#define OP_FT_NOT		"10100"
#define AOP_FT_NOT		"not"
#define OP_FT_AND		"10101"
#define AOP_FT_AND		"and"
#define OP_FT_IMPL		"11011"
#define AOP_FT_IMPL		"impl"

#define OP_OR			"00101"
#define AOP_OR			"or"
#define OP_EQUIVALENT		"00111"
#define AOP_EQUIVALENT		"equ"

	// past time operations
#define OP_PT_Y		"01000"
#define AOP_PT_Y	"previously"
#define OP_PT_O		"01001"
#define AOP_PT_O	"once"
#define OP_PT_H		"01010"
#define AOP_PT_H	"historically"
#define OP_PT_S		"01110"
#define AOP_PT_S	"since"

	// metric past and future time operations
	// intervals
#define OP_PT_HJ	"10010"
#define AOP_PT_HJ	"boxdot"
#define OP_PT_OJ	"10000"
#define AOP_PT_OJ	"diamonddot"
#define OP_PT_SJ	"10011"
#define AOP_PT_SJ	"since"

#define OP_FT_GJ	"10111"
#define AOP_FT_GJ	"boxdot"
#define OP_FT_FJ	"11001"
#define AOP_FT_FJ	"diamonddot"
#define OP_FT_UJ	"11010"
#define AOP_FT_UJ	"until"


	// end time points
#define OP_PT_HT	"10001"
#define AOP_PT_HT	"boxbox"
#define OP_PT_OT	"01111"
#define AOP_PT_OT	"diamondiamond"

#define OP_FT_GT	"10110"
#define AOP_FT_GT	"boxbox"
#define OP_FT_FT	"11000"
#define AOP_FT_FT	"diamondiamond"

	// SW load operator
#define OP_FT_LOD	"11100"
#define AOP_FT_LOD	"load_ft"


//---------------------------------------------
typedef enum {
	OPC_START = 0,
	OPC_END,
	OPC_END_SEQUENCE	,
	OPC_NOP	,
	OPC_NOT	,
	OPC_AND	,
	OPC_OR	,
	OPC_IMPL	,
	OPC_FT_NOT	,
	OPC_FT_AND	,
	OPC_FT_IMPL	,
	OPC_EQUIVALENT,
	// past time operations
	OPC_PT_Y	,
	OPC_PT_O	,
	OPC_PT_H	,
	OPC_PT_S	,
	// metric past and future time operations
	// intervals
	OPC_PT_HJ,
	OPC_PT_OJ,
	OPC_PT_SJ,
	OPC_FT_GJ,
	OPC_FT_FJ,
	OPC_FT_UJ,
	// end time points
	OPC_PT_HT,
	OPC_PT_OT,
	OPC_FT_GT,
	OPC_FT_FT,
	OPC_FT_LOD
	} t_op;

