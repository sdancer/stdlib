defmodule GleamStdLib do
  import Kernel, except: [{:inspect, 1}]

  def inspect(a) do
    Kernel.inspect(a)
  end

  def dec2hex(x) do
    cond do
      x >= 0 && x <= 9 -> x
      x >= 10 && x <= 15 -> x + ?A - 10
    end
  end

  def hex2dec(x) do
    cond do
      x >= ?0 && x <= ?9 -> x - ?0
      x >= ?A && x <= ?F -> x - ?A + 10
      x >= ?a && x <= ?f -> x - ?a + 10
    end
  end

  defmacro is_hex_digit(c) do
    (?0 <= c and c <= ?9) or
      (?a <= c and c <= ?f) or
      (?A <= c and c <= ?F)
  end

  def is_lowercase_char(x), do: x > 96 && x < 123
  def is_underscore_char(x), do: x == 95
  def is_digit_char(x), do: x > 47 && x < 58

  def print(string) do
    :io.put_chars(string)
  end

  def println(string) do
    :io.put_chars([string, ?\n])
  end

  def print_error(string) do
    :io.put_chars(:standard_error, string)
  end

  def println_error(string) do
    :io.put_chars(:standard_error, [string, ?\n])
  end

  def ok(n) do
    %{__module__: :prelude, __type__: Ok, field_0: n}
  end

  def error(n) do
    %{__module__: :prelude, __type__: Error, field_0: n}
  end

  def parse_query(query) do
    case :uri_string.dissect_query(query) do
      {:error, _, _} ->
        error(nil)

      pairs ->
        pairs1 =
          :lists.map(
            fn
              {k, true} -> {k, <<"">>}
              pair -> pair
            end,
            pairs
          )

        ok(pairs1)
    end
  end

  def percent_encode(binary) do
    percent_encode(binary, <<>>)
  end

  def percent_encode(<<>>, acc) do
    acc
  end

  def percent_encode(<<h, t::binary>>, acc) do
    case percent_ok(h) do
      true ->
        percent_encode(t, <<acc::binary, h>>)

      false ->
        <<a::4, b::4>> = <<h>>
        percent_encode(t, <<acc::binary, ?%, dec2hex(a), dec2hex(b)>>)
    end
  end

  def percent_decode(cs) do
    percent_decode(cs, <<>>)
  end

  def percent_decode(<<?%, c0, c1, cs::binary>>, acc)
      when ((?0 <= c0 and c0 <= ?9) or
              (?a <= c0 and c0 <= ?f) or
              (?A <= c0 and c0 <= ?F)) and
             ((?0 <= c1 and c1 <= ?9) or
                (?a <= c1 and c1 <= ?f) or
                (?A <= c1 and c1 <= ?F)) do
    b = hex2dec(c0) * 16 + hex2dec(c1)
    percent_decode(cs, <<acc::binary, b>>)
  end

  def percent_decode(<<c, cs::binary>>, acc) do
    percent_decode(cs, <<acc::binary, c>>)
  end

  def percent_decode(<<>>, acc) do
    check_utf8(acc)
  end

  def percent_ok(?!), do: true
  def percent_ok(?$), do: true
  def percent_ok(?'), do: true
  def percent_ok(?(), do: true
  def percent_ok(?)), do: true
  def percent_ok(?*), do: true
  def percent_ok(?+), do: true
  def percent_ok(?-), do: true
  def percent_ok(?.), do: true
  def percent_ok(?_), do: true
  def percent_ok(?~), do: true
  def percent_ok(c) when ?0 <= c and c <= ?9, do: true
  def percent_ok(c) when ?A <= c and c <= ?Z, do: true
  def percent_ok(c) when ?a <= c and c <= ?z, do: true
  def percent_ok(_), do: false

  def uppercase(x), do: x - 32

  def map_get(map, key) do
    case Map.fetch(map, key) do
      {:ok, value} -> {:ok, value}
      :error -> {:error, nil}
    end
  end

  def iodata_append(iodata, string), do: [iodata, string]

  def identity(x), do: x

  def decode_error_msg(expected, data) when is_binary(expected) do
    decode_error(expected, classify_dynamic(data))
  end

  def decode_error(expected, got) when is_binary(expected) and is_binary(got) do
    {:error, [{:decode_error, expected, got, []}]}
  end

  def classify_dynamic(nil), do: "Nil"
  def classify_dynamic(x) when is_atom(x), do: "Atom"
  def classify_dynamic(x) when is_binary(x), do: "String"
  def classify_dynamic(x) when is_bitstring(x), do: "BitArray"
  def classify_dynamic(x) when is_integer(x), do: "Int"
  def classify_dynamic(x) when is_float(x), do: "Float"
  def classify_dynamic(x) when is_list(x), do: "List"
  def classify_dynamic(x) when is_boolean(x), do: "Bool"
  def classify_dynamic(x) when is_map(x), do: "Map"

  def classify_dynamic(x) when is_tuple(x) do
    "Tuple of #{tuple_size(x)} elements"
  end

  def classify_dynamic(x) when is_function(x), do: "Function"
  def classify_dynamic(_), do: "Some other type"

  def decode_map(data) when is_map(data), do: {:ok, data}
  def decode_map(data), do: decode_error_msg("Map", data)

  def decode_bit_array(data) when is_bitstring(data), do: {:ok, data}
  def decode_bit_array(data), do: decode_error_msg("BitArray", data)

  def decode_int(data) when is_integer(data), do: {:ok, data}
  def decode_int(data), do: decode_error_msg("Int", data)

  def decode_float(data) when is_float(data), do: {:ok, data}
  def decode_float(data), do: decode_error_msg("Float", data)

  def decode_bool(data) when is_boolean(data), do: {:ok, data}
  def decode_bool(data), do: decode_error_msg("Bool", data)

  def decode_list(data) when is_list(data), do: {:ok, data}
  def decode_list(data), do: decode_error_msg("List", data)

  def decode_field(data, key) when is_map(data) do
    case Map.fetch(data, key) do
      {:ok, value} -> {:ok, {:some, value}}
      _ -> {:ok, :none}
    end
  end

  def decode_field(data, _), do: decode_error_msg("Map", data)

  def size_of_tuple(data), do: tuple_size(data)

  def tuple_get(_tup, index) when index < 0, do: {:error, nil}
  def tuple_get(data, index) when index >= tuple_size(data), do: {:error, nil}
  def tuple_get(data, index), do: {:ok, elem(index + 1, data)}

  def decode_tuple(data) when is_tuple(data), do: {:ok, data}
  def decode_tuple(data), do: decode_error_msg("Tuple", data)

  def decode_tuple2({_, _} = a), do: {:ok, a}
  def decode_tuple2([a, b]), do: {:ok, {a, b}}
  def decode_tuple2(data), do: decode_error_msg("Tuple of 2 elements", data)

  def decode_tuple3({_, _, _} = a), do: {:ok, a}
  def decode_tuple3([a, b, c]), do: {:ok, {a, b, c}}
  def decode_tuple3(data), do: decode_error_msg("Tuple of 3 elements", data)

  def decode_tuple4({_, _, _, _} = a), do: {:ok, a}
  def decode_tuple4([a, b, c, d]), do: {:ok, {a, b, c, d}}
  def decode_tuple4(data), do: decode_error_msg("Tuple of 4 elements", data)

  def decode_tuple5({_, _, _, _, _} = a), do: {:ok, a}
  def decode_tuple5([a, b, c, d, e]), do: {:ok, {a, b, c, d, e}}
  def decode_tuple5(data), do: decode_error_msg("Tuple of 5 elements", data)

  def decode_tuple6({_, _, _, _, _, _} = a), do: {:ok, a}
  def decode_tuple6([a, b, c, d, e, f]), do: {:ok, {a, b, c, d, e, f}}
  def decode_tuple6(data), do: decode_error_msg("Tuple of 6 elements", data)

  def decode_option(term, f) do
    decode = fn inner ->
      case f.(inner) do
        {:ok, decoded} -> {:ok, {:some, decoded}}
        error -> error
      end
    end

    case term do
      :undefined -> {:ok, :none}
      :error -> {:ok, :none}
      :null -> {:ok, :none}
      :none -> {:ok, :none}
      nil -> {:ok, :none}
      {:some, inner} -> decode.(inner)
      _ -> decode.(term)
    end
  end

  def decode_result(term) do
    case term do
      {:ok, inner} -> {:ok, {:ok, inner}}
      :ok -> {:ok, {:ok, nil}}
      {:error, inner} -> {:ok, {:error, inner}}
      :error -> {:ok, {:error, nil}}
      _ -> decode_error_msg("Result", term)
    end
  end

  def int_from_base_string(string, base) do
    case Integer.parse(string, base) do
      {int, _} when is_integer(int) ->
        {:ok, int}

      _ ->
        {:error, nil}
    end
  end

  def parse_int(string) do
    case Integer.parse(string) do
      {int, _} when is_integer(int) ->
        {:ok, int}

      _ ->
        {:error, nil}
    end
  end

  def parse_float(string) do
    case String.to_float(string) do
      {float, _} when is_float(float) -> {:ok, float}
      _ -> {:error, nil}
    end
  end

  def less_than(lhs, rhs), do: lhs < rhs

  def string_starts_with(_, <<>>), do: true
  def string_starts_with(string, prefix) when byte_size(prefix) > byte_size(string), do: false

  def string_starts_with(string, prefix) do
    prefix_size = byte_size(prefix)
    prefix == :binary.part(string, 0, prefix_size)
  end

  def string_ends_with(_, <<>>), do: true
  def string_ends_with(string, suffix) when byte_size(suffix) > byte_size(string), do: false

  def string_ends_with(string, suffix) do
    suffix_size = byte_size(suffix)
    suffix == :binary.part(string, byte_size(string) - suffix_size, suffix_size)
  end

  def string_pad(string, length, dir, pad_string) do
    chars =
      case dir do
        Right ->
          String.pad_trailing(string, length, pad_string)

        Left ->
          String.pad_trailing("", length, pad_string) <> string
      end

    case :unicode.characters_to_binary(chars) do
      bin when is_binary(bin) -> bin
      _ -> {:error, {:gleam_error, {:string_invalid_utf8, :error}}}
    end
  end

  def string_pop_grapheme(string) do
    case String.next_grapheme(string) do
      {next, rest} -> ok({next, rest})
      _ -> error(nil)
    end
  end

  def bit_array_concat(bit_arrays), do: :binary.list_to_bin(bit_arrays)

  def bit_array_slice(bin, pos, len) do
    try do
      {:ok, :binary.part(bin, pos, len)}
    rescue
      ArgumentError -> {:error, nil}
    end
  end

  def bit_array_int_to_u32(i) when 0 <= i and i < 4_294_967_296, do: {:ok, <<i::32>>}
  def bit_array_int_to_u32(_), do: {:error, nil}

  def bit_array_int_from_u32(<<i::32>>), do: {:ok, i}
  def bit_array_int_from_u32(_), do: {:error, nil}

  def compile_regex(string, options) do
    {:options, caseless, multiline} = options
    options_list = [:unicode, :ucp, caseless && :caseless, multiline && :multiline]
    filtered_options = Enum.filter(options_list, &(&1 != false))

    case :re.compile(string, filtered_options) do
      {:ok, mp} -> {:ok, mp}
      {:error, {str, pos}} -> {:error, {:compile_error, str, pos}}
    end
  end

  def regex_check(regex, string), do: :re.run(string, regex) != :nomatch

  def regex_split(regex, string), do: :re.split(string, regex)

  def regex_submatches(_, {-1, 0}), do: :none

  def regex_submatches(string, {start, length}) do
    binary_slice = :binary.part(string, {start, length})

    case binary_slice == "" do
      true -> :none
      false -> {:some, binary_slice}
    end
  end

  def regex_matches(string, [{start, length} | submatches]) do
    submatches1 = Enum.map(submatches, fn x -> regex_submatches(string, x) end)
    {:match, :binary.part(string, start, length), submatches1}
  end

  def regex_scan(regex, string) do
    case :re.run(string, regex, [:global]) do
      {:match, captured} ->
        Enum.map(captured, fn x -> regex_matches(string, x) end)

      :nomatch ->
        []
    end
  end

  def base_decode64(s) do
    try do
      {:ok, :base64.decode(s)}
    rescue
      _ -> {:error, nil}
    end
  end

  def wrap_list(x) when is_list(x), do: x
  def wrap_list(x), do: [x]

  def check_utf8(cs) do
    case :unicode.characters_to_list(cs) do
      {:incomplete, _, _} -> {:error, nil}
      {:error, _, _} -> {:error, nil}
      _ -> {:ok, cs}
    end
  end

  def uri_parse(string) do
    case :uri_string.parse(string) do
      {:error, _, _} ->
        {:error, nil}

      uri ->
        {:ok,
         {:uri, maps_get_optional(uri, :scheme), maps_get_optional(uri, :userinfo),
          maps_get_optional(uri, :host), maps_get_optional(uri, :port),
          maps_get_or(uri, :path, <<>>), maps_get_optional(uri, :query),
          maps_get_optional(uri, :fragment)}}
    end
  end

  def maps_get_optional(map, key) do
    try do
      {:some, Map.get(map, key)}
    rescue
      _ -> :none
    end
  end

  def maps_get_or(map, key, default) do
    try do
      Map.get(map, key)
    rescue
      _ -> default
    end
  end

  def float_to_string(float) when is_float(float) do
    :erlang.iolist_to_binary(:io_lib_format.fwrite_g(float))
  end

  def utf_codepoint_list_to_string(list) do
    case :unicode.characters_to_binary(list) do
      {:error, _} -> {:error, {:gleam_error, {:string_invalid_utf8, list}}}
      binary -> binary
    end
  end

  def crop_string(string, prefix) do
    case :string.find(string, prefix) do
      :nomatch -> string
      new -> new
    end
  end

  def contains_string(string, substring) do
    is_binary(:string.find(string, substring))
  end

  def base16_decode(string) do
    try do
      {:ok, :binary.decode_hex(string)}
    rescue
      _ -> {:error, nil}
    end
  end
end
