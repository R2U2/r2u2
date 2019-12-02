-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : filter_pkg.vhd
-- Author     : Andreas Hagmann <ahagmann@ecs.tuwien.ac.at>
-- Copyright  : 2012-10, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: filter components
------------------------------------------------------------------------------- 

library ieee;
use ieee.std_logic_1164.all;

package filter_pkg is

  component lowpass is
    generic (
      DATA_WIDTH    : integer := 16;
      FILTER_WEIGHT : integer := 1;
      FILTER_LEN    : integer := 8
      );
    port (clk        : in  std_logic;   -- System clock
          rst_n      : in  std_logic;   -- System reset
          sample_clk : in  std_logic;
          data_in    : in  std_logic_vector(DATA_WIDTH-1 downto 0);
          data_out   : out std_logic_vector(DATA_WIDTH-1 downto 0)
          );
  end component;

  component max is
    generic (
      DATA_WIDTH : integer := 16
      );
    port (clk        : in  std_logic;   -- System clock
          rst_n      : in  std_logic;   -- System reset
          sample_clk : in  std_logic;
          data_in    : in  std_logic_vector(DATA_WIDTH-1 downto 0);
          data_out   : out std_logic_vector(DATA_WIDTH-1 downto 0)
          );
  end component;

  component min is
    generic (
      DATA_WIDTH : integer := 16
      );
    port (clk        : in  std_logic;   -- System clock
          rst_n      : in  std_logic;   -- System reset
          sample_clk : in  std_logic;
          data_in    : in  std_logic_vector(DATA_WIDTH-1 downto 0);
          data_out   : out std_logic_vector(DATA_WIDTH-1 downto 0)
          );
  end component;

  component moving_min is
    generic (
      DATA_WIDTH : integer := 16;
      FILTER_LEN : integer := 64
      );
    port (clk        : in  std_logic;   -- System clock
          rst_n      : in  std_logic;   -- System reset
          sample_clk : in  std_logic;
          data_in    : in  std_logic_vector(DATA_WIDTH-1 downto 0);
          data_out   : out std_logic_vector(DATA_WIDTH-1 downto 0)
          );
  end component;

  component moving_max is
    generic (
      DATA_WIDTH : integer := 16;
      FILTER_LEN : integer := 64
      );
    port (clk        : in  std_logic;   -- System clock
          rst_n      : in  std_logic;   -- System reset
          sample_clk : in  std_logic;
          data_in    : in  std_logic_vector(DATA_WIDTH-1 downto 0);
          data_out   : out std_logic_vector(DATA_WIDTH-1 downto 0)
          );
  end component;

  component moving_avg is
    generic (
      DATA_WIDTH : integer := 16;
      FILTER_LEN : integer := 64
      );
    port (clk        : in  std_logic;   -- System clock
          rst_n      : in  std_logic;   -- System reset
          sample_clk : in  std_logic;
          data_in    : in  std_logic_vector(DATA_WIDTH-1 downto 0);
          data_out   : out std_logic_vector(DATA_WIDTH-1 downto 0)
          );
  end component;

  component rate is
    generic(
      DATA_WIDTH : integer := 16
      );
    port(
      clk        : in  std_logic;
      rst_n      : in  std_logic;
      sample_clk : in  std_logic;
      --data
      data_in    : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      data_out   : out std_logic_vector(DATA_WIDTH-1 downto 0)
      );
  end component;
  
  component mac3 is
  generic(
  DATA_WIDTH : integer := 16
  );
  port(
  clk : in std_logic;
  rst_n : in std_logic;
  sample_clk : in std_logic;
  --data
  data_in_1 : in std_logic_vector(DATA_WIDTH-1 downto 0);
  data_in_2 : in std_logic_vector(DATA_WIDTH-1 downto 0);
  data_in_3 : in std_logic_vector(DATA_WIDTH-1 downto 0);
  data_out  : out std_logic_vector((2*DATA_WIDTH)-1 downto 0)
  );
end component;

end filter_pkg;
