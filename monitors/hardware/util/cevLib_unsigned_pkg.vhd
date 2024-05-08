------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : cevLib_unsigned_pkg.vhd
-- Author     : Thomas Reinbacher, Johannes Geist
-- Copyright  : 2011, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: Some useful functions for synthesis                                  
-------------------------------------------------------------------------------  
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

package cevLib_unsigned_pkg is

  subtype slv is std_logic_vector;

  function "+"(L : std_logic_vector; R : std_logic_vector) return std_logic_vector;
  function "+"(L : std_logic_vector; R : natural) return std_logic_vector;
  function "+"(L : natural; R : std_logic_vector) return std_logic_vector;

  function "-"(L : std_logic_vector; R : std_logic_vector) return std_logic_vector;
  function "-"(L : std_logic_vector; R : natural) return std_logic_vector;
  function "-"(L : natural; R : std_logic_vector) return std_logic_vector;

  function "="(L : std_logic_vector; R : std_logic_vector) return boolean;
  function "="(L : natural; R : std_logic_vector) return boolean;
  function "="(L : std_logic_vector; R : natural) return boolean;

  function "/="(L : std_logic_vector; R : std_logic_vector) return boolean;
  function "/="(L : natural; R : std_logic_vector) return boolean;
  function "/="(L : std_logic_vector; R : natural) return boolean;

  function "<="(L : std_logic_vector; R : std_logic_vector) return boolean;
  function "<="(L : std_logic_vector; R : natural) return boolean;
  function "<="(L : natural; R : std_logic_vector) return boolean;

  function ">="(L : std_logic_vector; R : std_logic_vector) return boolean;
  function ">="(L : natural; R : std_logic_vector) return boolean;
  function ">="(L : std_logic_vector; R : natural) return boolean;

  function "<"(L : std_logic_vector; R : std_logic_vector) return boolean;
  function "<"(L : natural; R : std_logic_vector) return boolean;
  function "<"(L : std_logic_vector; R : natural) return boolean;

  function ">"(L : std_logic_vector; R : std_logic_vector) return boolean;
  function ">"(L : natural; R : std_logic_vector) return boolean;
  function ">"(L : std_logic_vector; R : natural) return boolean;

  function max(L : std_logic_vector; R : std_logic_vector) return std_logic_vector;
  function max(L : std_logic_vector; R : natural) return std_logic_vector;
  function max(L : natural; R : std_logic_vector) return std_logic_vector;
  function max(L : natural; R : natural) return natural;

  function minimum(L : std_logic_vector; R : std_logic_vector) return std_logic_vector;
  function minimum(L : std_logic_vector; R : natural) return std_logic_vector;
  function minimum(L : natural; R : std_logic_vector) return std_logic_vector;
  function minimum(L : natural; R : natural) return natural;

  function cnt_ones(A : std_logic_vector; res_size : natural) return std_logic_vector;
  function cnt_ones(A : std_logic_vector) return natural;

  function cnt_zeros(A : std_logic_vector; res_size : natural) return std_logic_vector;
  function cnt_zeros(A : std_logic_vector) return natural;

  function has_one(A  : std_logic_vector) return boolean;
  function has_zero(A : std_logic_vector) return boolean;

  function shift_left(S  : std_logic_vector; amount : natural) return std_logic_vector;
  function shift_right(S : std_logic_vector; amount : natural) return std_logic_vector;

  function reverse(A : std_logic_vector) return std_logic_vector;

  function conv_to_integer (source : std_logic_vector) return integer;
  function conv_to_slv (source     : integer; size : integer) return std_logic_vector;

  function condAssign(b : boolean; V1 : integer; V2 : integer) return integer;

  function "*"(operand1, operand2 : std_logic_vector)return std_logic_vector;

  function bool_to_sl(b : boolean) return std_logic;

  function is_falling(old_val, new_val  : std_logic) return boolean;
  function is_rising(old_val, new_val   : std_logic) return boolean;
  function is_toggling(old_val, new_val : std_logic) return boolean;

end cevLib_unsigned_pkg;

package body cevLib_unsigned_pkg is

  function condAssign(b : boolean; V1 : integer; V2 : integer) return integer is
    variable result : integer;
  begin
    if b = true then
      result := V1;
    else
      result := V2;
    end if;
    return result;
  end function condAssign;

  function "+"(L : std_logic_vector; R : std_logic_vector) return std_logic_vector is
    constant length : integer := max(L'length, R'length);
    variable result : unsigned(length-1 downto 0);
  begin
    result := unsigned(L) + unsigned(R);
    return std_logic_vector(result);
  end function "+";

  function "+"(L : natural; R : std_logic_vector) return std_logic_vector is
    variable result : unsigned(R'length-1 downto 0);
  begin
    result := L + unsigned(R);
    return std_logic_vector(result);
  end function "+";

  function "+"(L : std_logic_vector; R : natural) return std_logic_vector is
    variable result : unsigned(L'length-1 downto 0);
  begin
    result := unsigned(L) + R;
    return std_logic_vector(result);
  end function "+";

  function "-"(L : std_logic_vector; R : std_logic_vector) return std_logic_vector is
    constant length : integer := max(L'length, R'length);
    variable result : unsigned(length-1 downto 0);
  begin
    result := unsigned(L) - unsigned(R);
    return std_logic_vector(result);
  end function "-";

  function "-"(L : natural; R : std_logic_vector) return std_logic_vector is
    variable result : unsigned(R'length-1 downto 0);
  begin
    result := L - unsigned(R);
    return std_logic_vector(result);
  end function "-";

  function "-"(L : std_logic_vector; R : natural) return std_logic_vector is
    variable result : unsigned(L'length-1 downto 0);
  begin
    result := unsigned(L) - R;
    return std_logic_vector(result);
  end function "-";

  function "=" (L : std_logic_vector; R : std_logic_vector) return boolean is
    variable result : boolean;
  begin
    result := unsigned(L) = unsigned(R);
    return result;
  end "=";

  function "=" (L : natural; R : std_logic_vector) return boolean is
    variable result : boolean;
  begin
    result := L = unsigned(R);
    return result;
  end "=";

  function "=" (L : std_logic_vector; R : natural) return boolean is
    variable result : boolean;
  begin
    result := unsigned(L) = R;
    return result;
  end "=";

  function "/=" (L : std_logic_vector; R : std_logic_vector) return boolean is
    variable result : boolean;
  begin
    result := unsigned(L) /= unsigned(R);
    return result;
  end "/=";

  function "/=" (L : natural; R : std_logic_vector) return boolean is
    variable result : boolean;
  begin
    result := L /= unsigned(R);
    return result;
  end "/=";

  function "/=" (L : std_logic_vector; R : natural) return boolean is
    --constant length : integer := L'length;
    variable result : boolean;
  begin
    result := unsigned(L) /= R;
    return result;
  end "/=";

  function "<" (L : std_logic_vector; R : std_logic_vector) return boolean is
    variable result : boolean;
  begin
    result := unsigned(L) < unsigned(R);
    return result;
  end "<";

  function "<" (L : natural; R : std_logic_vector) return boolean is
    --constant length : integer := R'length;
    variable result : boolean;
  begin
    result := L < unsigned(R);
    return result;
  end "<";

  function "<" (L : std_logic_vector; R : natural) return boolean is
    --constant length : integer := L'length;
    variable result : boolean;
  begin
    result := unsigned(L) < R;
    return result;
  end "<";

  function ">" (L : std_logic_vector; R : std_logic_vector) return boolean is
    variable result : boolean;
  begin
    result := unsigned(L) > unsigned(R);
    return result;
  end ">";

  function ">" (L : natural; R : std_logic_vector) return boolean is
    variable result : boolean;
  begin
    result := L > unsigned(R);
    return result;
  end ">";

  function ">" (L : std_logic_vector; R : natural) return boolean is
    variable result : boolean;
  begin
    result := unsigned(L) > R;
    return result;
  end ">";

  function ">=" (L : std_logic_vector; R : std_logic_vector) return boolean is
    variable result : boolean;
  begin
    result := unsigned(L) >= unsigned(R);
    return result;
  end ">=";

  function ">=" (L : std_logic_vector; R : natural) return boolean is
    variable result : boolean;
  begin
    result := unsigned(L) >= R;
    return result;
  end ">=";

  function ">=" (L : natural; R : std_logic_vector) return boolean is
    variable result : boolean;
  begin
    result := L >= unsigned(R);
    return result;
  end ">=";

  function "<=" (L : std_logic_vector; R : std_logic_vector) return boolean is
    variable result : boolean;
  begin
    result := unsigned(L) <= unsigned(R);
    return result;
  end "<=";

  function "<=" (L : std_logic_vector; R : natural) return boolean is
    variable result : boolean;
  begin
    result := unsigned(L) <= R;
    return result;
  end "<=";

  function "<=" (L : natural; R : std_logic_vector) return boolean is
    variable result : boolean;
  begin
    result := L <= unsigned(R);
    return result;
  end "<=";

  function max(L : std_logic_vector; R : std_logic_vector) return std_logic_vector is
    constant length    : integer := max(L'length, R'length);
    variable ret_value : std_logic_vector(length-1 downto 0);
  begin
    if L > R then
      ret_value := L;
    else
      ret_value := R;
    end if;
    return ret_value;
  end function max;

  function max(L : natural; R : std_logic_vector) return std_logic_vector is
    constant length    : integer := R'length;
    variable ret_value : std_logic_vector(length-1 downto 0);
  begin
    if L > R then
      ret_value := std_logic_vector(to_unsigned(L, length));
    else
      ret_value := R;
    end if;
    return ret_value;
  end function max;

  function max(L : std_logic_vector; R : natural) return std_logic_vector is
    constant length    : integer := L'length;
    variable ret_value : std_logic_vector(length-1 downto 0);
  begin
    if L > R then
      ret_value := L;
    else
      ret_value := std_logic_vector(to_unsigned(R, length));
    end if;
    return ret_value;
  end function max;

  function max(L : natural; R : natural) return natural is
    variable ret_value : natural;
  begin
    if L > R then
      ret_value := L;
    else
      ret_value := R;
    end if;
    return ret_value;
  end function max;

  function minimum(L : std_logic_vector; R : std_logic_vector) return std_logic_vector is
    constant length    : integer := max(L'length, R'length);
    variable ret_value : std_logic_vector(length-1 downto 0);
  begin
    if L < R then
      ret_value := L;
    else
      ret_value := R;
    end if;
    return ret_value;
  end function minimum;

  function minimum(L : natural; R : std_logic_vector) return std_logic_vector is
    constant length    : integer := R'length;
    variable ret_value : std_logic_vector(length-1 downto 0);
  begin
    if L < R then
      ret_value := std_logic_vector(to_unsigned(L, length));
    else
      ret_value := R;
    end if;
    return ret_value;
  end function minimum;

  function minimum(L : std_logic_vector; R : natural) return std_logic_vector is
    constant length    : integer := L'length;
    variable ret_value : std_logic_vector(length-1 downto 0);
  begin
    if L < R then
      ret_value := L;
    else
      ret_value := std_logic_vector(to_unsigned(R, length));
    end if;
    return ret_value;
  end function minimum;

  function minimum(L : natural; R : natural) return natural is
    variable ret_value : natural;
  begin
    if L < R then
      ret_value := L;
    else
      ret_value := R;
    end if;
    return ret_value;
  end function minimum;

  function cnt_ones(A : std_logic_vector; res_size : natural) return std_logic_vector is
    variable ret_value : natural := 0;
  begin
    for i in A'range loop
      if A(i) = '1' then
        ret_value := ret_value + 1;
      end if;
    end loop;
    return std_logic_vector(to_unsigned(ret_value, res_size));
  end function cnt_ones;

  function cnt_ones(A : std_logic_vector) return natural is
    variable ret_value : natural := 0;
  begin
    for i in A'range loop
      if A(i) = '1' then
        ret_value := ret_value + 1;
      end if;
    end loop;
    return ret_value;
  end function cnt_ones;

  function cnt_zeros(A : std_logic_vector; res_size : natural) return std_logic_vector is
    variable ret_value : natural := 0;
  begin
    for i in A'range loop
      if A(i) = '0' then
        ret_value := ret_value + 1;
      end if;
    end loop;
    return std_logic_vector(to_unsigned(ret_value, res_size));
  end function cnt_zeros;

  function cnt_zeros(A : std_logic_vector) return natural is
    variable ret_value : natural := 0;
  begin
    for i in A'range loop
      if A(i) = '0' then
        ret_value := ret_value + 1;
      end if;
    end loop;
    return ret_value;
  end function cnt_zeros;

  function has_one(A : std_logic_vector) return boolean is
    variable ret_value : boolean := false;
  begin
    for i in A'range loop
      if A(i) = '1' then
        ret_value := true;
      end if;
    end loop;
    return ret_value;
  end function has_one;

  function has_zero(A : std_logic_vector) return boolean is
    variable ret_value : boolean := false;
  begin
    for i in A'range loop
      if A(i) = '0' then
        ret_value := true;
      end if;
    end loop;
    return ret_value;
  end function has_zero;

  function shift_left(S : std_logic_vector; amount : natural) return std_logic_vector is
    variable result : std_logic_vector((S'length - 1) downto 0);
  begin
    result := std_logic_vector(shift_left(unsigned(S), amount));
    return result;
  end function shift_left;

  function shift_right(S : std_logic_vector; amount : natural) return std_logic_vector is
    variable result : std_logic_vector((S'length - 1) downto 0);
  begin
    result := std_logic_vector(shift_right(unsigned(S), amount));
    return result;
  end function shift_right;

  function reverse(A : std_logic_vector) return std_logic_vector is
    variable reversed : std_logic_vector(A'reverse_range);
    variable result   : std_logic_vector(A'range);
  begin
    for i in A'range loop
      reversed(i) := A(i);
    end loop;
    result := reversed;
    return result;
  end function reverse;

  function conv_to_integer (source : std_logic_vector) return integer is
    variable result : integer;
  begin
    result := to_integer(unsigned(source));
    return result;
  end conv_to_integer;

  function conv_to_slv (source : integer; size : integer) return std_logic_vector is
    variable result : std_logic_vector(size-1 downto 0);
  begin
    result := std_logic_vector(to_unsigned(source, size));
    return result;
  end conv_to_slv;

  function "*" (operand1, operand2 : std_logic_vector) return std_logic_vector is
    constant result_width : natural := operand1'length+operand2'length;
    variable result       : unsigned(result_width-1 downto 0);
  begin
    result := unsigned(operand1) * unsigned(operand2);
    return std_logic_vector(result);
  end "*";

  function bool_to_sl(b : boolean) return std_logic is
    variable result : std_logic;
  begin
    if b = true then
      result := '1';
    else
      result := '0';
    end if;
    return result;
  end function bool_to_sl;

  function is_toggling(old_val, new_val : std_logic) return boolean is
    variable result : boolean := true;
  begin
    if ((old_val xor new_val) = '1') then
      result := true;
    end if;
    return result;
  end function is_toggling;

  function is_rising(old_val, new_val : std_logic) return boolean is
    variable result : boolean := true;
  begin
    result := is_toggling(old_val, new_val) and (new_val = '1');
    return result;
  end function is_rising;

  function is_falling(old_val, new_val : std_logic) return boolean is
    variable result : boolean := true;
  begin
    result := is_toggling(old_val, new_val) and not (new_val = '1');
    return result;
  end function is_falling;
end cevLib_unsigned_pkg;
