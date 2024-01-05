
local LibDeflate = {}

local _pow2 = {}
local _byte_to_char = {}
local _reverse_bits_tbl = {}

local _literal_deflate_code_to_base_len = {
	3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31,
	35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258,
}
local _literal_deflate_code_to_extra_bitlen = {
	0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2,
	3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0,
}
local _dist_deflate_code_to_base_dist = {
	[0] = 1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193,
	257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145,
	8193, 12289, 16385, 24577,
}
local _dist_deflate_code_to_extra_bitlen = {
	[0] = 0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6,
	7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13,
}
local _rle_codes_huffman_bitlen_order = {16, 17, 18,
	0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15,
}
local _fix_block_literal_huffman_code
local _fix_block_literal_huffman_to_deflate_code
local _fix_block_literal_huffman_bitlen
local _fix_block_literal_huffman_bitlen_count
local _fix_block_dist_huffman_code
local _fix_block_dist_huffman_to_deflate_code
local _fix_block_dist_huffman_bitlen
local _fix_block_dist_huffman_bitlen_count
for i = 0, 255 do
	_byte_to_char[i] = string.char(i)
end
do
	local pow = 1
	for i = 0, 32 do
		_pow2[i] = pow
		pow = pow * 2
	end
end
for i = 1, 9 do
	_reverse_bits_tbl[i] = {}
	for j=0, _pow2[i+1]-1 do
		local reverse = 0
		local value = j
		for _ = 1, i do
			-- The following line is equivalent to "res | (code %2)" in C.
			reverse = reverse - reverse%2
			+ (((reverse%2==1) or (value % 2) == 1) and 1 or 0)
			value = (value-value%2)/2
			reverse = reverse * 2
		end
		_reverse_bits_tbl[i][j] = (reverse-reverse%2)/2
	end
end

function LibDeflate:Adler32(str)
	if type(str) ~= "string" then
		error(("Usage: LibDeflate:Adler32(str):"
			.." 'str' - string expected got '%s'."):format(type(str)), 2)
	end
	local strlen = #str
	local i = 1
	local a = 1
	local b = 0
	while i <= strlen - 15 do
		local x1, x2, x3, x4, x5, x6, x7, x8,
		x9, x10, x11, x12, x13, x14, x15, x16 = string.byte(str, i, i+15)
		b = (b+16*a+16*x1+15*x2+14*x3+13*x4+12*x5+11*x6+10*x7+9*x8+8*x9
			+7*x10+6*x11+5*x12+4*x13+3*x14+2*x15+x16)%65521
		a = (a+x1+x2+x3+x4+x5+x6+x7+x8+x9+x10+x11+x12+x13+x14+x15+x16)%65521
		i =  i + 16
	end
	while i <= strlen do
		local x = string.byte(str, i, i)
		a = (a + x) % 65521
		b = (b + a) % 65521
		i = i + 1
	end
	return (b*65536+a) % 4294967296
end
local function IsEqualAdler32(actual, expected)
	return (actual % 4294967296) == (expected % 4294967296)
end
function LibDeflate:CreateDictionary(str, strlen, adler32)
	if type(str) ~= "string" then
		error(("Usage: LibDeflate:CreateDictionary(str, strlen, adler32):"
			.." 'str' - string expected got '%s'."):format(type(str)), 2)
	end
	if type(strlen) ~= "number" then
		error(("Usage: LibDeflate:CreateDictionary(str, strlen, adler32):"
			.." 'strlen' - number expected got '%s'."):format(
				type(strlen)), 2)
	end
	if type(adler32) ~= "number" then
		error(("Usage: LibDeflate:CreateDictionary(str, strlen, adler32):"
			.." 'adler32' - number expected got '%s'."):format(
				type(adler32)), 2)
	end
	if strlen ~= #str then
		error(("Usage: LibDeflate:CreateDictionary(str, strlen, adler32):"
			.." 'strlen' does not match the actual length of 'str'."
			.." 'strlen': %u, '#str': %u ."
			.." Please check if 'str' is modified unintentionally.")
			:format(strlen, #str))
	end
	if strlen == 0 then
		error(("Usage: LibDeflate:CreateDictionary(str, strlen, adler32):"
			.." 'str' - Empty string is not allowed."), 2)
	end
	if strlen > 32768 then
		error(("Usage: LibDeflate:CreateDictionary(str, strlen, adler32):"
			.." 'str' - string longer than 32768 bytes is not allowed."
			.." Got %d bytes."):format(strlen), 2)
	end
	local actual_adler32 = self:Adler32(str)
	if not IsEqualAdler32(adler32, actual_adler32) then
		error(("Usage: LibDeflate:CreateDictionary(str, strlen, adler32):"
			.." 'adler32' does not match the actual adler32 of 'str'."
			.." 'adler32': %u, 'Adler32(str)': %u ."
			.." Please check if 'str' is modified unintentionally.")
			:format(adler32, actual_adler32))
	end
	local dictionary = {}
	dictionary.adler32 = adler32
	dictionary.hash_tables = {}
	dictionary.string_table = {}
	dictionary.strlen = strlen
	local string_table = dictionary.string_table
	local hash_tables = dictionary.hash_tables
	string_table[1] = string.byte(str, 1, 1)
	string_table[2] = string.byte(str, 2, 2)
	if strlen >= 3 then
		local i = 1
		local hash = string_table[1]*256+string_table[2]
		while i <= strlen - 2 - 3 do
			local x1, x2, x3, x4 = string.byte(str, i+2, i+5)
			string_table[i+2] = x1
			string_table[i+3] = x2
			string_table[i+4] = x3
			string_table[i+5] = x4
			hash = (hash*256+x1)%16777216
			local t = hash_tables[hash]
			if not t then
				t = {}
				hash_tables[hash] = t
			end
			t[#t+1] = i-strlen
			i = i + 1
			hash = (hash*256+x2)%16777216
			t = hash_tables[hash]
			if not t then
				t = {}
				hash_tables[hash] = t
			end
			t[#t+1] = i-strlen
			i = i + 1
			hash = (hash*256+x3)%16777216
			t = hash_tables[hash]
			if not t then
				t = {}
				hash_tables[hash] = t
			end
			t[#t+1] = i-strlen
			i = i + 1
			hash = (hash*256+x4)%16777216
			t = hash_tables[hash]
			if not t then
				t = {}
				hash_tables[hash] = t
			end
			t[#t+1] = i-strlen
			i = i + 1
		end
		while i <= strlen - 2 do
			local x = string.byte(str, i+2)
			string_table[i+2] = x
			hash = (hash*256+x)%16777216
			local t = hash_tables[hash]
			if not t then
				t = {}
				hash_tables[hash] = t
			end
			t[#t+1] = i-strlen
			i = i + 1
		end
	end
	return dictionary
end
local function IsValidDictionary(dictionary)
	if type(dictionary) ~= "table" then
		return false, ("'dictionary' - table expected got '%s'.")
		:format(type(dictionary))
	end
	if type(dictionary.adler32) ~= "number"
		or type(dictionary.string_table) ~= "table"
		or type(dictionary.strlen) ~= "number"
		or dictionary.strlen <= 0
		or dictionary.strlen > 32768
		or dictionary.strlen ~= #dictionary.string_table
		or type(dictionary.hash_tables) ~= "table"
	then
		return false, ("'dictionary' - corrupted dictionary.")
		:format(type(dictionary))
	end
	return true, ""
end
local _compression_level_configs = {
	[0] = {false, nil, 0, 0, 0}, -- level 0, no compression
	[1] = {false, nil, 4, 8, 4}, -- level 1, similar to zlib level 1
	[2] = {false, nil, 5, 18, 8}, -- level 2, similar to zlib level 2
	[3] = {false, nil, 6, 32, 32},	-- level 3, similar to zlib level 3
	[4] = {true, 4,	4, 16, 16},	-- level 4, similar to zlib level 4
	[5] = {true, 8,	16,	32,	32}, -- level 5, similar to zlib level 5
	[6] = {true, 8,	16,	128, 128}, -- level 6, similar to zlib level 6
	[7] = {true, 8,	32,	128, 256}, -- (SLOW) level 7, similar to zlib level 7
	[8] = {true, 32, 128, 258, 1024} , --(SLOW) level 8,similar to zlib level 8
	[9] = {true, 32, 258, 258, 4096}, -- (VERY SLOW) level 9, similar to zlib level 9
}
local function IsValidArguments(str,
	check_dictionary, dictionary,
	check_configs, configs)
	if type(str) ~= "string" then
		return false,
			("'str' - string expected got '%s'."):format(type(str))
	end
	if check_dictionary then
		local dict_valid, dict_err = IsValidDictionary(dictionary)
		if not dict_valid then
			return false, dict_err
		end
	end
	if check_configs then
		local type_configs = type(configs)
		if type_configs ~= "nil" and type_configs ~= "table" then
			return false,
				("'configs' - nil or table expected got '%s'.")
			:format(type(configs))
		end
		if type_configs == "table" then
			for k, v in pairs(configs) do
				if k ~= "level" and k ~= "strategy" then
					return false,
						("'configs' - unsupported table key in the configs: '%s'.")
					:format(k)
				elseif k == "level" and not _compression_level_configs[v] then
					return false,
						("'configs' - unsupported 'level': %s."):format(tostring(v))
				elseif k == "strategy" and v ~= "fixed" and v ~= "huffman_only"
					and v ~= "dynamic" then
					-- random_block_type is for testing purpose
					return false, ("'configs' - unsupported 'strategy': '%s'.")
					:format(tostring(v))
				end
			end
		end
	end
	return true, ""
end

local function GetHuffmanCodeFromBitlen(bitlen_counts, symbol_bitlens
	, max_symbol, max_bitlen)
	local huffman_code = 0
	local next_codes = {}
	local symbol_huffman_codes = {}
	for bitlen = 1, max_bitlen do
		huffman_code = (huffman_code+(bitlen_counts[bitlen-1] or 0))*2
		next_codes[bitlen] = huffman_code
	end
	for symbol = 0, max_symbol do
		local bitlen = symbol_bitlens[symbol]
		if bitlen then
			huffman_code = next_codes[bitlen]
			next_codes[bitlen] = huffman_code + 1
			if bitlen <= 9 then
				symbol_huffman_codes[symbol] = _reverse_bits_tbl[bitlen][huffman_code]
			else
				local reverse = 0
				for _ = 1, bitlen do
					reverse = reverse - reverse%2
					+ (((reverse%2==1)
						or (huffman_code % 2) == 1) and 1 or 0)
					huffman_code = (huffman_code-huffman_code%2)/2
					reverse = reverse*2
				end
				symbol_huffman_codes[symbol] = (reverse-reverse%2)/2
			end
		end
	end
	return symbol_huffman_codes
end

local function CreateReader(input_string)
	local input = input_string
	local input_strlen = #input_string
	local input_next_byte_pos = 1
	local cache_bitlen = 0
	local cache = 0
	local function ReadBits(bitlen)
		local rshift_mask = _pow2[bitlen]
		local code
		if bitlen <= cache_bitlen then
			code = cache % rshift_mask
			cache = (cache - code) / rshift_mask
			cache_bitlen = cache_bitlen - bitlen
		else
			local lshift_mask = _pow2[cache_bitlen]
			local byte1, byte2, byte3, byte4 = string.byte(input
				, input_next_byte_pos, input_next_byte_pos+3)
			cache = cache + ((byte1 or 0)+(byte2 or 0)*256
				+ (byte3 or 0)*65536+(byte4 or 0)*16777216)*lshift_mask
			input_next_byte_pos = input_next_byte_pos + 4
			cache_bitlen = cache_bitlen + 32 - bitlen
			code = cache % rshift_mask
			cache = (cache - code) / rshift_mask
		end
		return code
	end
	local function ReadBytes(bytelen, buffer, buffer_size)
		assert(cache_bitlen % 8 == 0, '')
		local byte_from_cache = (cache_bitlen/8 < bytelen)
		and (cache_bitlen/8) or bytelen
		for _=1, byte_from_cache do
			local byte = cache % 256
			buffer_size = buffer_size + 1
			buffer[buffer_size] = string.char(byte)
			cache = (cache - byte) / 256
		end
		cache_bitlen = cache_bitlen - byte_from_cache*8
		bytelen = bytelen - byte_from_cache
		if (input_strlen - input_next_byte_pos - bytelen + 1) * 8
			+ cache_bitlen < 0 then
			return -1 -- out of input
		end
		for i=input_next_byte_pos, input_next_byte_pos+bytelen-1 do
			buffer_size = buffer_size + 1
			buffer[buffer_size] = string.sub(input, i, i)
		end
		input_next_byte_pos = input_next_byte_pos + bytelen
		return buffer_size
	end
	local function Decode(huffman_bitlen_counts, huffman_symbols, min_bitlen)
		local code = 0
		local first = 0
		local index = 0
		local count
		if min_bitlen > 0 then
			if cache_bitlen < 15 and input then
				local lshift_mask = _pow2[cache_bitlen]
				local byte1, byte2, byte3, byte4 =
					string.byte(input, input_next_byte_pos
						, input_next_byte_pos+3)
				cache = cache + ((byte1 or 0)+(byte2 or 0)*256
					+(byte3 or 0)*65536+(byte4 or 0)*16777216)*lshift_mask
				input_next_byte_pos = input_next_byte_pos + 4
				cache_bitlen = cache_bitlen + 32
			end
			local rshift_mask = _pow2[min_bitlen]
			cache_bitlen = cache_bitlen - min_bitlen
			code = cache % rshift_mask
			cache = (cache - code) / rshift_mask
			code = _reverse_bits_tbl[min_bitlen][code]
			count = huffman_bitlen_counts[min_bitlen]
			if code < count then
				return huffman_symbols[code]
			end
			index = count
			first = count * 2
			code = code * 2
		end
		for bitlen = min_bitlen+1, 15 do
			local bit
			bit = cache % 2
			cache = (cache - bit) / 2
			cache_bitlen = cache_bitlen - 1
			code = (bit==1) and (code + 1 - code % 2) or code
			count = huffman_bitlen_counts[bitlen] or 0
			local diff = code - first
			if diff < count then
				return huffman_symbols[index + diff]
			end
			index = index + count
			first = first + count
			first = first * 2
			code = code * 2
		end
		return -10
	end
	local function ReaderBitlenLeft()
		return (input_strlen - input_next_byte_pos + 1) * 8 + cache_bitlen
	end
	local function SkipToByteBoundary()
		local skipped_bitlen = cache_bitlen%8
		local rshift_mask = _pow2[skipped_bitlen]
		cache_bitlen = cache_bitlen - skipped_bitlen
		cache = (cache - cache % rshift_mask) / rshift_mask
	end
	return ReadBits, ReadBytes, Decode, ReaderBitlenLeft, SkipToByteBoundary
end
local function CreateDecompressState(str, dictionary)
	local ReadBits, ReadBytes, Decode, ReaderBitlenLeft, SkipToByteBoundary = CreateReader(str)
	return {
		ReadBits = ReadBits,
		ReadBytes = ReadBytes,
		Decode = Decode,
		ReaderBitlenLeft = ReaderBitlenLeft,
		SkipToByteBoundary = SkipToByteBoundary,
		buffer_size = 0,
		buffer = {},
		result_buffer = {},
		dictionary = dictionary,
	}
end

local function GetHuffmanForDecode(huffman_bitlens, max_symbol, max_bitlen)
	local huffman_bitlen_counts = {}
	local min_bitlen = max_bitlen
	for symbol = 0, max_symbol do
		local bitlen = huffman_bitlens[symbol] or 0
		min_bitlen = (bitlen > 0 and bitlen < min_bitlen)
		and bitlen or min_bitlen
		huffman_bitlen_counts[bitlen] = (huffman_bitlen_counts[bitlen] or 0)+1
	end
	if huffman_bitlen_counts[0] == max_symbol+1 then -- No Codes
		return 0, huffman_bitlen_counts, {}, 0 -- Complete, but decode will fail
	end
	local left = 1
	for len = 1, max_bitlen do
		left = left * 2
		left = left - (huffman_bitlen_counts[len] or 0)
		if left < 0 then
			return left
		end
	end
	local offsets = {}
	offsets[1] = 0
	for len = 1, max_bitlen-1 do
		offsets[len + 1] = offsets[len] + (huffman_bitlen_counts[len] or 0)
	end
	local huffman_symbols = {}
	for symbol = 0, max_symbol do
		local bitlen = huffman_bitlens[symbol] or 0
		if bitlen ~= 0 then
			local offset = offsets[bitlen]
			huffman_symbols[offset] = symbol
			offsets[bitlen] = offsets[bitlen] + 1
		end
	end
	return left, huffman_bitlen_counts, huffman_symbols, min_bitlen
end
local function DecodeUntilEndOfBlock(state, lcodes_huffman_bitlens
	, lcodes_huffman_symbols, lcodes_huffman_min_bitlen
	, dcodes_huffman_bitlens, dcodes_huffman_symbols
	, dcodes_huffman_min_bitlen)
	local buffer, buffer_size, ReadBits, Decode, ReaderBitlenLeft
	, result_buffer =
		state.buffer, state.buffer_size, state.ReadBits, state.Decode
	, state.ReaderBitlenLeft, state.result_buffer
	local dictionary = state.dictionary
	local dict_string_table
	local dict_strlen
	local buffer_end = 1
	if dictionary and not buffer[0] then
		dict_string_table = dictionary.string_table
		dict_strlen = dictionary.strlen
		buffer_end = -dict_strlen + 1
		for i=0, (-dict_strlen+1)<-257 and -257 or (-dict_strlen+1), -1 do
			buffer[i] = _byte_to_char[dict_string_table[dict_strlen+i]]
		end
	end
	repeat
		local symbol = Decode(lcodes_huffman_bitlens
			, lcodes_huffman_symbols, lcodes_huffman_min_bitlen)
		if symbol < 0 or symbol > 285 then
			return -10
		elseif symbol < 256 then
			buffer_size = buffer_size + 1
			buffer[buffer_size] = _byte_to_char[symbol]
		elseif symbol > 256 then
			symbol = symbol - 256
			local bitlen = _literal_deflate_code_to_base_len[symbol]
			bitlen = (symbol >= 8)
			and (bitlen
				+ ReadBits(_literal_deflate_code_to_extra_bitlen[symbol]))
			or bitlen
			symbol = Decode(dcodes_huffman_bitlens, dcodes_huffman_symbols
				, dcodes_huffman_min_bitlen)
			if symbol < 0 or symbol > 29 then
				return -10
			end
			local dist = _dist_deflate_code_to_base_dist[symbol]
			dist = (dist > 4) and (dist
			+ ReadBits(_dist_deflate_code_to_extra_bitlen[symbol])) or dist
			local char_buffer_index = buffer_size-dist+1
			if char_buffer_index < buffer_end then
				return -11
			end
			if char_buffer_index >= -257 then
				for _=1, bitlen do
					buffer_size = buffer_size + 1
					buffer[buffer_size] = buffer[char_buffer_index]
					char_buffer_index = char_buffer_index + 1
				end
			else
				char_buffer_index = dict_strlen + char_buffer_index
				for _=1, bitlen do
					buffer_size = buffer_size + 1
					buffer[buffer_size] =
						_byte_to_char[dict_string_table[char_buffer_index]]
					char_buffer_index = char_buffer_index + 1
				end
			end
		end
		if ReaderBitlenLeft() < 0 then
			return 2
		end
		if buffer_size >= 65536 then
			result_buffer[#result_buffer+1] =
				table.concat(buffer, "", 1, 32768)
			for i=32769, buffer_size do
				buffer[i-32768] = buffer[i]
			end
			buffer_size = buffer_size - 32768
			buffer[buffer_size+1] = nil
		end
	until symbol == 256
	state.buffer_size = buffer_size
	return 0
end
local function DecompressStoreBlock(state)
	local buffer, buffer_size, ReadBits, ReadBytes, ReaderBitlenLeft
	, SkipToByteBoundary, result_buffer =
		state.buffer, state.buffer_size, state.ReadBits, state.ReadBytes
	, state.ReaderBitlenLeft, state.SkipToByteBoundary, state.result_buffer
	SkipToByteBoundary()
	local bytelen = ReadBits(16)
	if ReaderBitlenLeft() < 0 then
		return 2
	end
	local bytelenComp = ReadBits(16)
	if ReaderBitlenLeft() < 0 then
		return 2
	end
	if bytelen % 256 + bytelenComp % 256 ~= 255 then
		return -2
	end
	if (bytelen-bytelen % 256)/256
		+ (bytelenComp-bytelenComp % 256)/256 ~= 255 then
		return -2
	end
	buffer_size = ReadBytes(bytelen, buffer, buffer_size)
	if buffer_size < 0 then
		return 2
	end
	if buffer_size >= 65536 then
		result_buffer[#result_buffer+1] = table.concat(buffer, "", 1, 32768)
		for i=32769, buffer_size do
			buffer[i-32768] = buffer[i]
		end
		buffer_size = buffer_size - 32768
		buffer[buffer_size+1] = nil
	end
	state.buffer_size = buffer_size
	return 0
end
local function DecompressFixBlock(state)
	return DecodeUntilEndOfBlock(state
		, _fix_block_literal_huffman_bitlen_count
		, _fix_block_literal_huffman_to_deflate_code, 7
		, _fix_block_dist_huffman_bitlen_count
		, _fix_block_dist_huffman_to_deflate_code, 5)
end
local function DecompressDynamicBlock(state)
	local ReadBits, Decode = state.ReadBits, state.Decode
	local nlen = ReadBits(5) + 257
	local ndist = ReadBits(5) + 1
	local ncode = ReadBits(4) + 4
	if nlen > 286 or ndist > 30 then
		return -3
	end
	local rle_codes_huffman_bitlens = {}
	for i = 1, ncode do
		rle_codes_huffman_bitlens[_rle_codes_huffman_bitlen_order[i]] =
			ReadBits(3)
	end
	local rle_codes_err, rle_codes_huffman_bitlen_counts,
	rle_codes_huffman_symbols, rle_codes_huffman_min_bitlen =
		GetHuffmanForDecode(rle_codes_huffman_bitlens, 18, 7)
	if rle_codes_err ~= 0 then -- Require complete code set here
		return -4
	end
	local lcodes_huffman_bitlens = {}
	local dcodes_huffman_bitlens = {}
	local index = 0
	while index < nlen + ndist do
		local symbol
		local bitlen
		symbol = Decode(rle_codes_huffman_bitlen_counts
			, rle_codes_huffman_symbols, rle_codes_huffman_min_bitlen)
		if symbol < 0 then
			return symbol -- Invalid symbol
		elseif symbol < 16 then
			if index < nlen then
				lcodes_huffman_bitlens[index] = symbol
			else
				dcodes_huffman_bitlens[index-nlen] = symbol
			end
			index = index + 1
		else
			bitlen = 0
			if symbol == 16 then
				if index == 0 then
					return -5
				end
				if index-1 < nlen then
					bitlen = lcodes_huffman_bitlens[index-1]
				else
					bitlen = dcodes_huffman_bitlens[index-nlen-1]
				end
				symbol = 3 + ReadBits(2)
			elseif symbol == 17 then
				symbol = 3 + ReadBits(3)
			else
				symbol = 11 + ReadBits(7)
			end
			if index + symbol > nlen + ndist then
				return -6
			end
			while symbol > 0 do
				symbol = symbol - 1
				if index < nlen then
					lcodes_huffman_bitlens[index] = bitlen
				else
					dcodes_huffman_bitlens[index-nlen] = bitlen
				end
				index = index + 1
			end
		end
	end
	if (lcodes_huffman_bitlens[256] or 0) == 0 then
		return -9
	end
	local lcodes_err, lcodes_huffman_bitlen_counts
	, lcodes_huffman_symbols, lcodes_huffman_min_bitlen =
		GetHuffmanForDecode(lcodes_huffman_bitlens, nlen-1, 15)
	if lcodes_err ~=0 and (lcodes_err < 0
		or nlen ~= (lcodes_huffman_bitlen_counts[0] or 0)
		+(lcodes_huffman_bitlen_counts[1] or 0)) then
		return -7
	end
	local dcodes_err, dcodes_huffman_bitlen_counts
	, dcodes_huffman_symbols, dcodes_huffman_min_bitlen =
		GetHuffmanForDecode(dcodes_huffman_bitlens, ndist-1, 15)
	if dcodes_err ~=0 and (dcodes_err < 0
		or ndist ~= (dcodes_huffman_bitlen_counts[0] or 0)
		+ (dcodes_huffman_bitlen_counts[1] or 0)) then
		return -8
	end
	return DecodeUntilEndOfBlock(state, lcodes_huffman_bitlen_counts
		, lcodes_huffman_symbols, lcodes_huffman_min_bitlen
		, dcodes_huffman_bitlen_counts, dcodes_huffman_symbols
		, dcodes_huffman_min_bitlen)
end
local function Inflate(state)
	local ReadBits = state.ReadBits
	local is_last_block
	while not is_last_block do
		is_last_block = (ReadBits(1) == 1)
		local block_type = ReadBits(2)
		local status
		if block_type == 0 then
			status = DecompressStoreBlock(state)
		elseif block_type == 1 then
			status = DecompressFixBlock(state)
		elseif block_type == 2 then
			status = DecompressDynamicBlock(state)
		else
			return nil, -1
		end
		if status ~= 0 then
			return nil, status
		end
	end
	state.result_buffer[#state.result_buffer+1] =
		table.concat(state.buffer, "", 1, state.buffer_size)
	local result = table.concat(state.result_buffer)
	return result
end

local function DecompressZlibInternal(str, dictionary)
	local state = CreateDecompressState(str, dictionary)
	local ReadBits = state.ReadBits
	local CMF = ReadBits(8)
	if state.ReaderBitlenLeft() < 0 then
		return nil, 2
	end
	local CM = CMF % 16
	local CINFO = (CMF - CM) / 16
	if CM ~= 8 then
		return nil, -12
	end
	if CINFO > 7 then
		return nil, -13
	end
	local FLG = ReadBits(8)
	if state.ReaderBitlenLeft() < 0 then
		return nil, 2
	end
	if (CMF*256+FLG)%31 ~= 0 then
		return nil, -14
	end
	local FDIST = ((FLG-FLG%32)/32 % 2)
	if FDIST == 1 then
		if not dictionary then
			return nil, -16
		end
		local byte3 = ReadBits(8)
		local byte2 = ReadBits(8)
		local byte1 = ReadBits(8)
		local byte0 = ReadBits(8)
		local actual_adler32 = byte3*16777216+byte2*65536+byte1*256+byte0
		if state.ReaderBitlenLeft() < 0 then
			return nil, 2
		end
		if not IsEqualAdler32(actual_adler32, dictionary.adler32) then
			return nil, -17
		end
	end
	local result, status = Inflate(state)
	if not result then
		return nil, status
	end
	state.SkipToByteBoundary()
	local adler_byte0 = ReadBits(8)
	local adler_byte1 = ReadBits(8)
	local adler_byte2 = ReadBits(8)
	local adler_byte3 = ReadBits(8)
	if state.ReaderBitlenLeft() < 0 then
		return nil, 2
	end
	local adler32_expected = adler_byte0*16777216
	+ adler_byte1*65536 + adler_byte2*256 + adler_byte3
	local adler32_actual = LibDeflate:Adler32(result)
	if not IsEqualAdler32(adler32_expected, adler32_actual) then
		return nil, -15
	end
	local bitlen_left = state.ReaderBitlenLeft()
	local bytelen_left = (bitlen_left - bitlen_left % 8) / 8
	return result, bytelen_left
end

function LibDeflate:DecompressZlib(str)
	local arg_valid, arg_err = IsValidArguments(str)
	if not arg_valid then
		error(("Usage: LibDeflate:DecompressZlib(str): "
			..arg_err), 2)
	end
	return DecompressZlibInternal(str)
end
function LibDeflate:DecompressZlibWithDict(str, dictionary)
	local arg_valid, arg_err = IsValidArguments(str, true, dictionary)
	if not arg_valid then
		error(("Usage: LibDeflate:DecompressZlibWithDict(str, dictionary): "
			..arg_err), 2)
	end
	return DecompressZlibInternal(str, dictionary)
end
do
	_fix_block_literal_huffman_bitlen = {}
	for sym=0, 143 do
		_fix_block_literal_huffman_bitlen[sym] = 8
	end
	for sym=144, 255 do
		_fix_block_literal_huffman_bitlen[sym] = 9
	end
	for sym=256, 279 do
		_fix_block_literal_huffman_bitlen[sym] = 7
	end
	for sym=280, 287 do
		_fix_block_literal_huffman_bitlen[sym] = 8
	end
	_fix_block_dist_huffman_bitlen = {}
	for dist=0, 31 do
		_fix_block_dist_huffman_bitlen[dist] = 5
	end
	local status
	status, _fix_block_literal_huffman_bitlen_count
	, _fix_block_literal_huffman_to_deflate_code =
		GetHuffmanForDecode(_fix_block_literal_huffman_bitlen, 287, 9)
	assert(status == 0, '')
	status, _fix_block_dist_huffman_bitlen_count,
		_fix_block_dist_huffman_to_deflate_code =
		GetHuffmanForDecode(_fix_block_dist_huffman_bitlen, 31, 5)
	assert(status == 0, '')
	_fix_block_literal_huffman_code =
		GetHuffmanCodeFromBitlen(_fix_block_literal_huffman_bitlen_count
			, _fix_block_literal_huffman_bitlen, 287, 9)
	_fix_block_dist_huffman_code =
		GetHuffmanCodeFromBitlen(_fix_block_dist_huffman_bitlen_count
			, _fix_block_dist_huffman_bitlen, 31, 5)
end
local _gsub_escape_table = {
	["\000"] = "%z", ["("] = "%(", [")"] = "%)", ["."] = "%.",
	["%"] = "%%", ["+"] = "%+", ["-"] = "%-", ["*"] = "%*",
	["?"] = "%?", ["["] = "%[", ["]"] = "%]", ["^"] = "%^",
	["$"] = "%$",
}
local function escape_for_gsub(str)
	return str:gsub("([%z%(%)%.%%%+%-%*%?%[%]%^%$])", _gsub_escape_table)
end
function LibDeflate:CreateCodec(reserved_chars, escape_chars
	, map_chars)
	if type(reserved_chars) ~= "string"
		or type(escape_chars) ~= "string"
		or type(map_chars) ~= "string" then
		error(
			"Usage: LibDeflate:CreateCodec(reserved_chars,"
			.." escape_chars, map_chars):"
			.." All arguments must be string.", 2)
	end
	if escape_chars == "" then
		return nil, "No escape characters supplied."
	end
	if #reserved_chars < #map_chars then
		return nil, "The number of reserved characters must be"
		.." at least as many as the number of mapped chars."
	end
	if reserved_chars == "" then
		return nil, "No characters to encode."
	end
	local encode_bytes = reserved_chars..escape_chars..map_chars
	local taken = {}
	for i = 1, #encode_bytes do
		local byte = string.byte(encode_bytes, i, i)
		if taken[byte] then
			return nil, "There must be no duplicate characters in the"
			.." concatenation of reserved_chars, escape_chars and"
			.." map_chars."
		end
		taken[byte] = true
	end
	local decode_patterns = {}
	local decode_repls = {}
	local encode_search = {}
	local encode_translate = {}
	if #map_chars > 0 then
		local decode_search = {}
		local decode_translate = {}
		for i = 1, #map_chars do
			local from = string.sub(reserved_chars, i, i)
			local to = string.sub(map_chars, i, i)
			encode_translate[from] = to
			encode_search[#encode_search+1] = from
			decode_translate[to] = from
			decode_search[#decode_search+1] = to
		end
		decode_patterns[#decode_patterns+1] =
			"([".. escape_for_gsub(table.concat(decode_search)).."])"
		decode_repls[#decode_repls+1] = decode_translate
	end
	local escape_char_index = 1
	local escape_char = string.sub(escape_chars
		, escape_char_index, escape_char_index)
	local r = 0
	local decode_search = {}
	local decode_translate = {}
	for i = 1, #encode_bytes do
		local c = string.sub(encode_bytes, i, i)
		if not encode_translate[c] then
			while r >= 256 or taken[r] do
				r = r + 1
				if r > 255 then -- switch to next escapeChar
					decode_patterns[#decode_patterns+1] =
						escape_for_gsub(escape_char)
						.."(["
						.. escape_for_gsub(table.concat(decode_search)).."])"
					decode_repls[#decode_repls+1] = decode_translate
					escape_char_index = escape_char_index + 1
					escape_char = string.sub(escape_chars, escape_char_index
						, escape_char_index)
					r = 0
					decode_search = {}
					decode_translate = {}
					if not escape_char or escape_char == "" then
						return nil, "Out of escape characters."
					end
				end
			end
			local char_r = _byte_to_char[r]
			encode_translate[c] = escape_char..char_r
			encode_search[#encode_search+1] = c
			decode_translate[char_r] = c
			decode_search[#decode_search+1] = char_r
			r = r + 1
		end
		if i == #encode_bytes then
			decode_patterns[#decode_patterns+1] =
				escape_for_gsub(escape_char).."(["
				.. escape_for_gsub(table.concat(decode_search)).."])"
			decode_repls[#decode_repls+1] = decode_translate
		end
	end
	local codec = {}
	local encode_pattern = "(["
	.. escape_for_gsub(table.concat(encode_search)).."])"
	local encode_repl = encode_translate
	function codec:Encode(str)
		if type(str) ~= "string" then
			error(("Usage: codec:Encode(str):"
				.." 'str' - string expected got '%s'."):format(type(str)), 2)
		end
		return string.gsub(str, encode_pattern, encode_repl)
	end
	local decode_tblsize = #decode_patterns
	local decode_fail_pattern = "(["
	.. escape_for_gsub(reserved_chars).."])"
	function codec:Decode(str)
		if type(str) ~= "string" then
			error(("Usage: codec:Decode(str):"
				.." 'str' - string expected got '%s'."):format(type(str)), 2)
		end
		if string.find(str, decode_fail_pattern) then
			return nil
		end
		for i = 1, decode_tblsize do
			str = string.gsub(str, decode_patterns[i], decode_repls[i])
		end
		return str
	end
	return codec
end

local _byte_to_6bit_char = {
	[0]="a", "b", "c", "d", "e", "f", "g", "h",
	"i", "j", "k", "l", "m", "n", "o", "p",
	"q", "r", "s", "t", "u", "v", "w", "x",
	"y", "z", "A", "B", "C", "D", "E", "F",
	"G", "H", "I", "J", "K", "L", "M", "N",
	"O", "P", "Q", "R", "S", "T", "U", "V",
	"W", "X", "Y", "Z", "0", "1", "2", "3",
	"4", "5", "6", "7", "8", "9", "(", ")",
}

local _6bit_to_byte = {
	[97]=0,[98]=1,[99]=2,[100]=3,[101]=4,[102]=5,[103]=6,[104]=7,
	[105]=8,[106]=9,[107]=10,[108]=11,[109]=12,[110]=13,[111]=14,[112]=15,
	[113]=16,[114]=17,[115]=18,[116]=19,[117]=20,[118]=21,[119]=22,[120]=23,
	[121]=24,[122]=25,[65]=26,[66]=27,[67]=28,[68]=29,[69]=30,[70]=31,
	[71]=32,[72]=33,[73]=34,[74]=35,[75]=36,[76]=37,[77]=38,[78]=39,
	[79]=40,[80]=41,[81]=42,[82]=43,[83]=44,[84]=45,[85]=46,[86]=47,
	[87]=48,[88]=49,[89]=50,[90]=51,[48]=52,[49]=53,[50]=54,[51]=55,
	[52]=56,[53]=57,[54]=58,[55]=59,[56]=60,[57]=61,[40]=62,[41]=63,
}

function LibDeflate:EncodeForPrint(str)
	if type(str) ~= "string" then
		error(("Usage: LibDeflate:EncodeForPrint(str):"
			.." 'str' - string expected got '%s'."):format(type(str)), 2)
	end
	local strlen = #str
	local strlenMinus2 = strlen - 2
	local i = 1
	local buffer = {}
	local buffer_size = 0
	while i <= strlenMinus2 do
		local x1, x2, x3 = string.byte(str, i, i+2)
		i = i + 3
		local cache = x1+x2*256+x3*65536
		local b1 = cache % 64
		cache = (cache - b1) / 64
		local b2 = cache % 64
		cache = (cache - b2) / 64
		local b3 = cache % 64
		local b4 = (cache - b3) / 64
		buffer_size = buffer_size + 1
		buffer[buffer_size] =
			_byte_to_6bit_char[b1].._byte_to_6bit_char[b2]
			.._byte_to_6bit_char[b3].._byte_to_6bit_char[b4]
	end
	local cache = 0
	local cache_bitlen = 0
	while i <= strlen do
		local x = string.byte(str, i, i)
		cache = cache + x * _pow2[cache_bitlen]
		cache_bitlen = cache_bitlen + 8
		i = i + 1
	end
	while cache_bitlen > 0 do
		local bit6 = cache % 64
		buffer_size = buffer_size + 1
		buffer[buffer_size] = _byte_to_6bit_char[bit6]
		cache = (cache - bit6) / 64
		cache_bitlen = cache_bitlen - 6
	end
	return table.concat(buffer)
end

function LibDeflate:DecodeForPrint(str)
	if type(str) ~= "string" then
		error(("Usage: LibDeflate:DecodeForPrint(str):"
			.." 'str' - string expected got '%s'."):format(type(str)), 2)
	end
	str = str:gsub("^[%c ]+", "")
	str = str:gsub("[%c ]+$", "")
	local strlen = #str
	if strlen == 1 then
		return nil
	end
	local strlenMinus3 = strlen - 3
	local i = 1
	local buffer = {}
	local buffer_size = 0
	while i <= strlenMinus3 do
		local x1, x2, x3, x4 = string.byte(str, i, i+3)
		x1 = _6bit_to_byte[x1]
		x2 = _6bit_to_byte[x2]
		x3 = _6bit_to_byte[x3]
		x4 = _6bit_to_byte[x4]
		if not (x1 and x2 and x3 and x4) then
			return nil
		end
		i = i + 4
		local cache = x1+x2*64+x3*4096+x4*262144
		local b1 = cache % 256
		cache = (cache - b1) / 256
		local b2 = cache % 256
		local b3 = (cache - b2) / 256
		buffer_size = buffer_size + 1
		buffer[buffer_size] =
			_byte_to_char[b1].._byte_to_char[b2].._byte_to_char[b3]
	end
	local cache  = 0
	local cache_bitlen = 0
	while i <= strlen do
		local x = string.byte(str, i, i)
		x =  _6bit_to_byte[x]
		if not x then
			return nil
		end
		cache = cache + x * _pow2[cache_bitlen]
		cache_bitlen = cache_bitlen + 6
		i = i + 1
	end
	while cache_bitlen >= 8 do
		local byte = cache % 256
		buffer_size = buffer_size + 1
		buffer[buffer_size] = _byte_to_char[byte]
		cache = (cache - byte) / 256
		cache_bitlen = cache_bitlen - 8
	end
	return table.concat(buffer)
end

-- Zlib.Decompress
_G.ZLibDecompress = function(compressedData)
	return LibDeflate:DecompressZlib(compressedData)
end
