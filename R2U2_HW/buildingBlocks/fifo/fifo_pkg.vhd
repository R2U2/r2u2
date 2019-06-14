-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : fifo_pkg.vhd
-- Author     : Daniel Schachinger      
-- Copyright  : 2011, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: fifo_pkg                                        
------------------------------------------------------------------------------- 

--synthesis VHDL_INPUT_VERSION VHDL_2008
library ieee;
use ieee.std_logic_1164.all;
use work.math_pkg.all;

package fifo_pkg is
  
  type fifo_ctrl_in_type is record
    rd : std_logic;
    wr : std_logic;
  end record;

  type fifo_ctrl_out_type is record
    empty : std_logic;
    full  : std_logic;
  end record;

  component fifo is
    generic
      (
        MIN_DEPTH  : integer;
        DATA_WIDTH : integer
        );
    port
      (
        clk   : in std_logic;
        res_n : in std_logic;

        data_out : out std_logic_vector(DATA_WIDTH - 1 downto 0);
        data_in  : in  std_logic_vector(DATA_WIDTH - 1 downto 0);

        ctrl_o : out fifo_ctrl_out_type;
        ctrl_i : in  fifo_ctrl_in_type
        );
  end component fifo;

  component fifo_w_element_cnt is
    generic
      (
        MIN_DEPTH  : integer;
        DATA_WIDTH : integer
        );
    port
      (
        clk      : in  std_logic;
        res_n    : in  std_logic;
        data_out : out std_logic_vector(DATA_WIDTH - 1 downto 0);
        data_in  : in  std_logic_vector(DATA_WIDTH - 1 downto 0);
        elements : out std_logic_vector(log2c(MIN_DEPTH)  downto 0);
        ctrl_o   : out fifo_ctrl_out_type;
        ctrl_i   : in  fifo_ctrl_in_type
        );
  end component fifo_w_element_cnt;  

end fifo_pkg;
