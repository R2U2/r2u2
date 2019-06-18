-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : at_checker_pkg.vhd
-- Author     : Andreas Hagmann <ahagmann@ecs.tuwien.ac.at>
-- Copyright  : 2012-10, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: The atomic checker components
------------------------------------------------------------------------------- 

library ieee;
use ieee.std_logic_1164.all;

package at_checker_pkg is

  subtype  r_operator_t is std_logic_vector(3-1 downto 0);
  constant GEQ : r_operator_t := "000";
  constant LEQ : r_operator_t := "001";
  constant GRE : r_operator_t := "010";
  constant LES : r_operator_t := "011";
  constant NEQ : r_operator_t := "100";
  constant EQU : r_operator_t := "101";

  subtype  a_operator_t is std_logic_vector(1 downto 0);
  constant A_ADD : a_operator_t := "00";
  constant A_SUB : a_operator_t := "01";
  constant A_DIF : a_operator_t := "10";

  --constant OP_WIDTH : integer := 32;
  constant OP_WIDTH : integer := 19;

  component at_checker is
    generic(
      IN_1_WIDTH : integer := 16;
      IN_2_WIDTH : integer := 16;
      ADDR       : integer := 0
      );
    port (
      clk          : in  std_logic;     -- System clock
      rst_n        : in  std_logic;     -- System reset
      -- config interface
      config_addr  : in  std_logic_vector(3-1 downto 0);
      config_data  : in  std_logic_vector(32-1 downto 0);
      config_write : in  std_logic;
      -- data
      in1          : in  std_logic_vector(IN_1_WIDTH-1 downto 0);
      in2          : in  std_logic_vector(IN_2_WIDTH-1 downto 0);
      ap           : out std_logic
      );
  end component;

component at_checker_unsigned is
    generic(
      IN_1_WIDTH : integer := 16;
      IN_2_WIDTH : integer := 16;
      ADDR       : integer := 0
      );
    port (
      clk          : in  std_logic;     -- System clock
      rst_n        : in  std_logic;     -- System reset
      -- config interface
      config_addr  : in  std_logic_vector(3-1 downto 0);
      config_data  : in  std_logic_vector(32-1 downto 0);
      config_write : in  std_logic;
      -- data
      in1          : in  std_logic_vector(IN_1_WIDTH-1 downto 0);
      in2          : in  std_logic_vector(IN_2_WIDTH-1 downto 0);
      ap           : out std_logic
      );
  end component; 
  
component at_checker_fp is
    generic(
      IN_1_WIDTH : integer := 16;
      IN_2_WIDTH : integer := 16;
      ADDR       : integer := 0
      );
    port (
      clk          : in  std_logic;     -- System clock
      rst_n        : in  std_logic;     -- System reset
      -- config interface
      config_addr  : in  std_logic_vector(3-1 downto 0);
      config_data  : in  std_logic_vector(32-1 downto 0);
      config_write : in  std_logic;
      -- data
      in1          : in  std_logic_vector(IN_1_WIDTH-1 downto 0);
      in2          : in  std_logic_vector(IN_2_WIDTH-1 downto 0);
      ap           : out std_logic
      );
  end component;  

end at_checker_pkg;
