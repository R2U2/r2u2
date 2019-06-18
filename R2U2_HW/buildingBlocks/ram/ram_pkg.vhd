-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : ram_pkg.vhd
-- Author     : Daniel Schachinger      
-- Copyright  : 2011, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: ram_pkg                                        
------------------------------------------------------------------------------- 

library ieee;
use ieee.std_logic_1164.all;
use work.math_pkg.all;

package ram_pkg is

  component ram is
    generic
      (
        ADDR_WIDTH : integer;
        DATA_WIDTH : integer
        );
    port
      (
        clk : in std_logic;

        raddr : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);
        rdata : out std_logic_vector(DATA_WIDTH - 1 downto 0);
        rd    : in  std_logic;

        waddr : in std_logic_vector(ADDR_WIDTH - 1 downto 0);
        wdata : in std_logic_vector(DATA_WIDTH - 1 downto 0);
        wr    : in std_logic
        );
  end component ram;

  component dp_ram_2w_2r is
    generic (
      ADDR_WIDTH : integer;   -- address width
      DATA_WIDTH : integer    -- data width
      );
    port (
        clk     : in  std_logic;                                  -- clock signal
        rdAddrA : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);  -- read address
        rdAddrB : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);  -- read address
        wrAddr  : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);  -- write address
        wrData  : in  std_logic_vector(DATA_WIDTH - 1 downto 0);  -- write data
        write   : in  std_logic;
        rdDataA    : out std_logic_vector(DATA_WIDTH - 1 downto 0);-- read data
        rdDataB    : out std_logic_vector(DATA_WIDTH - 1 downto 0)-- read data
      );
  end component;

  component ram_with_reset is
    generic
      (
        ADDR_WIDTH : integer;
        DATA_WIDTH : integer
        );
    port
      (
        clk     : in std_logic;
        reset_n : in std_logic;

        raddr : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);
        rdata : out std_logic_vector(DATA_WIDTH - 1 downto 0);
        rd    : in  std_logic;

        waddr : in std_logic_vector(ADDR_WIDTH - 1 downto 0);
        wdata : in std_logic_vector(DATA_WIDTH - 1 downto 0);
        wr    : in std_logic
        );
  end component ram_with_reset;

  component ram_with_double_memory_select is
    generic
      (
        ADDR_WIDTH             : integer;
        DATA_WIDTH             : integer;
        MEMBUS_RD_SELECT_WIDTH : integer;
        MEMBUS_WR_SELECT_WIDTH : integer;
        MEMBUS_RD_SELECT_ID    : std_logic_vector;
        MEMBUS_WR_SELECT_ID    : std_logic_vector
        );
    port
      (
        clk : in std_logic;

        raddr            : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);
        rdata            : out std_logic_vector(DATA_WIDTH - 1 downto 0);
        rd               : in  std_logic;
        rd_memory_select : in  std_logic_vector(MEMBUS_RD_SELECT_WIDTH - 1 downto 0);

        waddr            : in std_logic_vector(ADDR_WIDTH - 1 downto 0);
        wdata            : in std_logic_vector(DATA_WIDTH - 1 downto 0);
        wr               : in std_logic;
        wr_memory_select : in std_logic_vector(MEMBUS_WR_SELECT_WIDTH - 1 downto 0)
        );
  end component ram_with_double_memory_select;

  component ram_with_memory_select is
    generic
      (
        ADDR_WIDTH          : integer;
        DATA_WIDTH          : integer;
        MEMBUS_SELECT_WIDTH : integer;
        MEMBUS_SELECT_ID    : std_logic_vector
        );
    port
      (
        clk : in std_logic;

        raddr         : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);
        rdata         : out std_logic_vector(DATA_WIDTH - 1 downto 0);
        rd            : in  std_logic;
        memory_select : in  std_logic_vector(MEMBUS_SELECT_WIDTH - 1 downto 0);

        waddr : in std_logic_vector(ADDR_WIDTH - 1 downto 0);
        wdata : in std_logic_vector(DATA_WIDTH - 1 downto 0);
        wr    : in std_logic
        );
  end component ram_with_memory_select;

  component ram_with_reset_and_ack is
    generic
      (
        ADDR_WIDTH  : integer;
        DATA_WIDTH  : integer;
        RESET_VALUE : std_logic_vector
        );
    port
      (
        clk     : in std_logic;
        reset_n : in std_logic;

        raddr : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);
        rdata : out std_logic_vector(DATA_WIDTH - 1 downto 0);
        rd    : in  std_logic;
        rack  : out std_logic;

        waddr : in std_logic_vector(ADDR_WIDTH - 1 downto 0);
        wdata : in std_logic_vector(DATA_WIDTH - 1 downto 0);
        wr    : in std_logic
        );
  end component ram_with_reset_and_ack;
  
  component dp_ram_1w_3r_wt is
    generic (
      ADDR_WIDTH : integer;             -- address width
      DATA_WIDTH : integer              -- data width
      );
    port (
      clk     : in  std_logic;          -- clock signal
      rdAddrA : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);  -- read address
      rdAddrB : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);  -- read address
      rdAddrC : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);  -- read address
      wrAddr  : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);  -- write address
      wrData  : in  std_logic_vector(DATA_WIDTH - 1 downto 0);  -- write data
      write   : in  std_logic;
      rdDataA : out std_logic_vector(DATA_WIDTH - 1 downto 0);  -- read data
      rdDataB : out std_logic_vector(DATA_WIDTH - 1 downto 0);  -- read data
      rdDataC : out std_logic_vector(DATA_WIDTH - 1 downto 0)   -- read data
      );
  end component;
  
  component dp_ram is
    generic (
      ADDR_WIDTH : integer;                                    -- address width
      DATA_WIDTH : integer                                     -- data width
      );
    port (
      clk    : in  std_logic;                                  -- clock signal
      rdAddr : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);  -- read address
      wrAddr : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);  -- write address
      wrData : in  std_logic_vector(DATA_WIDTH - 1 downto 0);  -- write data
      write  : in  std_logic;                                  -- write signal
      rdData : out std_logic_vector(DATA_WIDTH - 1 downto 0)   -- read data
      );
  end component;

 component sp_ram is
 generic (
    ADDR_WIDTH : integer;                                    -- address width
    DATA_WIDTH : integer
    );
  port (
    clk     : in  std_logic;                                  -- clock signal
    addr    : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);  -- read address
    wrData  : in  std_logic_vector(DATA_WIDTH-1 downto 0);  -- write data
    write   : in  std_logic;
    rdData  : out std_logic_vector(DATA_WIDTH-1 downto 0)   -- read data
    );
  end component;


  component dp_ram_wt is
    generic (
      ADDR_WIDTH : integer;                                    -- address width
      DATA_WIDTH : integer                                     -- data width
      );
    port (
      clk    : in  std_logic;                                  -- clock signal
      rdAddr : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);  -- read address
      wrAddr : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);  -- write address
      wrData : in  std_logic_vector(DATA_WIDTH - 1 downto 0);  -- write data
      write  : in  std_logic;                                  -- write signal
      rdData : out std_logic_vector(DATA_WIDTH - 1 downto 0)   -- read data
      );
  end component;

  component sp_ram_wt is
    generic (
      ADDR_WIDTH : integer;                                    -- address width
      DATA_WIDTH : integer                                     -- data width
      );
    port (
      clk    : in  std_logic;                                  -- clock signal
      addr   : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);  -- read address
      wrData : in  std_logic_vector(DATA_WIDTH - 1 downto 0);  -- write data
      write  : in  std_logic;
      rdData : out std_logic_vector(DATA_WIDTH - 1 downto 0)   -- read data
      );
  end component;


end ram_pkg;
