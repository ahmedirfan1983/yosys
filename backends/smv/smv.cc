/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *  Copyright (C) 2014  Ahmed Irfan <irfan@fbk.eu>
 *  
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *  
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

////////////////////////
// SMV format dumper  //
//https://nuxmv.fbk.eu//
////////////////////////

#include "kernel/rtlil.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "kernel/log.h"
#include <string>
#include <math.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct SmvDumperConfig
{
	bool subckt_mode;
	bool conn_mode;
	bool impltf_mode;

	std::string buf_type, buf_in, buf_out;
	std::string true_type, true_out, false_type, false_out;

	SmvDumperConfig() : subckt_mode(false), conn_mode(false), impltf_mode(false) { }
};

struct WireInfo
{
	RTLIL::IdString cell_name;
	const RTLIL::SigChunk *chunk;

	WireInfo(RTLIL::IdString c, const RTLIL::SigChunk* ch) : cell_name(c), chunk(ch) { }
};

struct WireInfoOrder
{
	bool operator() (const WireInfo& x, const WireInfo& y) {
		return x.chunk < y.chunk;
	}
};

struct SmvDumper
{
	std::ostream &f;
	RTLIL::Module *module;
	RTLIL::Design *design;
	SmvDumperConfig *config;
	CellTypes ct;

	SigMap sigmap;
	std::map<RTLIL::IdString, std::set<WireInfo,WireInfoOrder>> inter_wire_map;//<wire, dependency list> for maping the intermediate wires that are output of some cell
  	std::map<RTLIL::IdString, std::pair<std::string, bool>> expr_ref;//mapping of ids to expression
	std::map<RTLIL::SigSpec, std::pair<std::string, bool>> sig_ref;//mapping of sigspec to the line_num of the btor file
	int line_num;//last line number of btor file
	std::string str;//temp string for writing file
	std::map<RTLIL::IdString, bool> basic_wires;//input wires and registers	
	RTLIL::IdString curr_cell; //current cell being dumped
	std::map<std::string, std::string> cell_type_translation; //RTLIL to SMV translation
	std::map<std::string, std::set<std::pair<int,int>>> mem_next; // memory (line_number)'s set of condition and write 
    	SmvDumper(std::ostream &f, RTLIL::Module *module, RTLIL::Design *design, SmvDumperConfig *config) :
    		f(f), module(module), design(design), config(config), ct(design), sigmap(module) {
		line_num=0;
		str.clear();
		for(auto it=module->wires_.begin(); it!=module->wires_.end(); ++it)
		{
			if(it->second->port_input)
			{
				basic_wires[it->first]=true;
			}
			else
			{
				basic_wires[it->first]=false;
			}
			inter_wire_map[it->first].clear();
		}
		curr_cell.clear();
		//unary
		cell_type_translation["$not"] = "!";
		cell_type_translation["$neg"] = "!";
		//binary
		cell_type_translation["$and"] = "&";
		cell_type_translation["$or"] = "|";
		cell_type_translation["$xor"] = "xor";
		cell_type_translation["$xnor"] = "xnor";
		cell_type_translation["$shr"] = ">>";
		cell_type_translation["$shl"] = "<<";
		cell_type_translation["$sshr"] = ">>";
		cell_type_translation["$sshl"] = "<<";
		cell_type_translation["$shift"] = ">>";
		cell_type_translation["$shiftx"] = ">>";
		cell_type_translation["$lt"] = "<";
		cell_type_translation["$le"] = "<=";
		cell_type_translation["$gt"] = ">";
		cell_type_translation["$ge"] = ">=";
		cell_type_translation["$eq"] = "=";
		cell_type_translation["$eqx"] = "=";
		cell_type_translation["$ne"] = "!=";
		cell_type_translation["$nex"] = "!=";
		cell_type_translation["$add"] = "+";
		cell_type_translation["$sub"] = "-";
		cell_type_translation["$mul"] = "*";
		cell_type_translation["$mod"] = "mod";
		cell_type_translation["$div"] = "/";
		//mux
		cell_type_translation["$mux"] = "?";
		//reg
		cell_type_translation["$dff"] = "next";
		cell_type_translation["$adff"] = "next";
		cell_type_translation["$dffsr"] = "next";
		//memories
		//nothing here
		//concat
		cell_type_translation["$concat"] = "::";

	}
	
	std::vector<std::string> cstr_buf;

	const char *cstr(const RTLIL::IdString id) {
		str = RTLIL::unescape_id(id);
		for (size_t i = 0; i < str.size(); ++i)
			if (str[i] == '#' || str[i] == '=')
				str[i] = '?';
		cstr_buf.push_back(str);
		return cstr_buf.back().c_str();
	}

  	const RTLIL::SigSpec* get_cell_output(RTLIL::Cell* cell) {	
		const RTLIL::SigSpec *output_sig = nullptr;
		if (cell->type == "$memrd")
		{
			output_sig = &cell->getPort(RTLIL::IdString("\\DATA"));
		}
		else if(cell->type == "$memwr" || cell->type == "$assert" || cell->type == "$meminit")
		{
			//no output                                                                                                                                                                                                          
		}
		else if(cell->type == "$dff" || cell->type == "$adff" || cell->type == "$dffsr" || cell->type == "$dlatch")
		{
			output_sig = &cell->getPort(RTLIL::IdString("\\Q"));
		}
		else
		{
			output_sig = &cell->getPort(RTLIL::IdString("\\Y"));
		}
		return output_sig;
	}

	bool is_bool_wire(RTLIL::Wire* wire) {
		return (basic_wires[wire->name] && wire->width == 1);
	}

	void dump_basic_wire(RTLIL::Wire* wire) {
		log_assert(basic_wires[wire->name]);
		log("writing basic wire %s\n", cstr(wire->name));
		if (is_bool_wire(wire))
			str = stringf("\"%s\" : boolean;", cstr(wire->name));
		else
			str = stringf("\"%s\" : word[%d];", cstr(wire->name), wire->width);
		f << stringf("%s\n", str.c_str());
		expr_ref[wire->name] = std::make_pair(stringf("\"%s\"", cstr(wire->name)),!is_bool_wire(wire));
	}
  
	std::string dump_wire(bool& output_type, RTLIL::Wire* wire, bool bv) {
		if(basic_wires[wire->name])
		{
			/*if(bv && wire->width == 1) 
			  {
			  str = stringf("__expr%d := word1(%s);", ++line_num, expr_ref[wire->name].c_str());
			  f << stringf("%s\n",str.c_str());
			  return stringf("__expr%d", line_num);
			  }
			  else
			*/
			output_type = expr_ref[wire->name].second;
			return expr_ref[wire->name].first;
		}
		else
		{
			log("case of non-basic wire - %s\n", cstr(wire->name));
			auto it = expr_ref.find(wire->name);
			if(it==std::end(expr_ref))
			{
				std::set<WireInfo, WireInfoOrder>& dep_set = inter_wire_map.at(wire->name);
				std::string wire_expr;
				int wire_width = 0;
				for(auto dep_set_it=dep_set.begin(); dep_set_it!=dep_set.end(); ++dep_set_it)
				{
					RTLIL::IdString cell_id = dep_set_it->cell_name;
					if(cell_id == curr_cell)
						break;
					log(" -- found cell %s\n", cstr(cell_id));
					RTLIL::Cell* cell = module->cells_.at(cell_id);
					const RTLIL::SigSpec* cell_output = get_cell_output(cell);
					std::string cell_expr = dump_cell(output_type, cell, bv);				

					if(dep_set.size()==1 && wire->width >= cell_output->size())
					{
						if(wire->width > cell_output->size()) {
							if(!output_type) {
								str = stringf("__exp%d := word1(%s);", ++line_num, cell_expr.c_str());
								f << stringf("%s\n", str.c_str());
								cell_expr = stringf("__expr%d", line_num);
							}
							str = stringf("__expr%d := resize(%s, %d);", ++line_num, cell_expr.c_str(), wire->width);
							f << stringf("%s\n", str.c_str());
							cell_expr = stringf("__expr%d", line_num);
							output_type = true;
						}
						wire_expr = cell_expr;
						break;
					}
					else
					{
						std::string prev_wire_expr; //previously dumped wire line
						int start_bit=0;
						for(unsigned j=0; j<cell_output->chunks().size(); ++j)
						{
							start_bit+=cell_output->chunks().at(j).width;
							if(cell_output->chunks().at(j).wire->name == wire->name)
							{
								prev_wire_expr = wire_expr;
								wire_expr = stringf("__expr%d", ++line_num);
								str = stringf("__expr%d := %s[%d:%d]; --wire", line_num, cell_expr.c_str(), start_bit-1, start_bit-cell_output->chunks().at(j).width);
								f << stringf("%s\n", str.c_str());
								wire_width += cell_output->chunks().at(j).width;
								if(!prev_wire_expr.empty())
								{
									++line_num;
									str = stringf("__expr%d := %s :: %s;", line_num, wire_expr.c_str(), prev_wire_expr.c_str());
									f << stringf("%s\n", str.c_str());
									wire_expr = stringf("__expr%d", line_num);
									output_type = true;
								}
							}
						}
					}
				}
				if(dep_set.size()==0)
				{
					log(" - checking sigmap\n");						
					log_abort();
					//RTLIL::SigSpec s = RTLIL::SigSpec(wire);
					//wire_expr = dump_sigspec(output_type, &s, s.size());
				}
				expr_ref[wire->name]=std::make_pair(wire_expr.c_str(), output_type);
				return wire_expr;
			}
			else 
			{
				log(" -- already processed wire\n");			
				output_type = it->second.second;
				return it->second.first;
			}
		}
		log_abort();
		return std::string();
	}
	
	void dump_memory(const RTLIL::Memory* memory)	{
		log("writing memory %s\n", cstr(memory->name));
		int address_bits = ceil(log(memory->size)/log(2));
		str = stringf("%s : array word[%d] of word[%d];", cstr(memory->name), address_bits, memory->width);
		f << stringf("%s\n", str.c_str());
		expr_ref[memory->name] = std::make_pair(cstr(memory->name), true);
	}

	std::string dump_memory_next(const RTLIL::Memory* memory) {
		auto mem_it = expr_ref.find(memory->name);
		if(mem_it==std::end(expr_ref))
		{
			log("can not write next of a memory that is not dumped yet\n");
			log_abort();
		}
		else
		{
			auto acond_list_it = mem_next.find(mem_it->second.first);
			if(acond_list_it!=std::end(mem_next))
			{
				std::set<std::pair<int,int>>& cond_list = acond_list_it->second;
				if(cond_list.empty())
				{
					return std::string();
				}
				auto it=cond_list.begin();
				++line_num;
				str = stringf("__expr%d := (case __expr%d: __expr%d; TRUE: %s; esac);", line_num, it->first, it->second, mem_it->second.first.c_str());
				f << stringf("%s\n", str.c_str());
				++it;
				for(; it!=cond_list.end(); ++it)
				{
					++line_num;
					str = stringf("__expr%d := (case __expr%d: __expr%d; TRUE: __expr%d; esac);", line_num, it->first, it->second, line_num-1);
					f << stringf("%s\n", str.c_str());
				}
				++line_num;
				str = stringf("__expr%d := next(%s) = __expr%d;", line_num, mem_it->second.first.c_str(), line_num-1);                                                                                                                 
				f << stringf("%s\n", str.c_str());
				return stringf("__expr%d", line_num);
			}
		}
		return std::string();
	}
	

	std::string dump_const(const RTLIL::Const* data, int width, int offset) {
		log("writing const \n");
		if((data->flags & RTLIL::CONST_FLAG_STRING) == 0)
		{
			if(width<0)
				width = data->bits.size() - offset;

			std::string data_str = data->as_string();
			//if(offset > 0)
			data_str = data_str.substr(offset, width);

			str = stringf("0ub%d_%s", width, data_str.c_str());
			return str;
		}
		else
			log("writing const error\n");		
		log_abort();
		return std::string();
	}
	
	std::string dump_sigchunk(bool& output_type, const RTLIL::SigChunk* chunk, bool bv) {
		log("writing sigchunk\n");
		std::string l;
		if(chunk->wire == NULL)
		{
			RTLIL::Const data_const(chunk->data);
			l=dump_const(&data_const, chunk->width, chunk->offset);
			output_type = true;
		}
		else
		{
			if (chunk->width == chunk->wire->width && chunk->offset == 0)
				l = dump_wire(output_type, chunk->wire, bv);
			else 
			{
				std::string wire_expr = dump_wire(output_type, chunk->wire, bv);
				log_assert(!wire_expr.empty());
				++line_num;
				str = stringf("__expr%d := %s[%d:%d]; --sigchunk", line_num, wire_expr.c_str(), 
					      chunk->width + chunk->offset - 1, chunk->offset);
				f << stringf("%s\n", str.c_str());
				l = stringf("__expr%d", line_num);
			}
		}
		return l;
	}

	std::string dump_sigspec(bool& output_type, const RTLIL::SigSpec* sig, int expected_width, bool bv) {
		log("writing sigspec width %d with expected_width %d\n", sig->size(), expected_width);
		RTLIL::SigSpec s = sigmap(*sig);
		std::string l;
		auto it = sig_ref.find(s);
		if(it == std::end(sig_ref))
		{
			if (s.is_chunk())
			{
				l = dump_sigchunk(output_type, &s.chunks().front(), bv);
			} 
			else 
			{
				std::string l1, l2;
				int w1, w2;
				l1 = dump_sigchunk(output_type, &s.chunks().front(), true);
				log_assert(!l1.empty());
				if(!output_type) {
					str = stringf("__expr%d := word1(%s);", ++line_num, l1.c_str());
					f << stringf("%s\n", str.c_str());
					l1 = stringf("__expr%d", line_num);
				}
				w1 = s.chunks().front().width;
				for (unsigned i=1; i < s.chunks().size(); ++i)
				{
					l2 = dump_sigchunk(output_type, &s.chunks().at(i), true);
					log_assert(!l2.empty());
					if(!output_type) {
						str = stringf("__expr%d := word1(%s);", ++line_num, l2.c_str());
						f << stringf("%s\n", str.c_str());
						l2 = stringf("__expr%d", line_num);
					}
					w2 = s.chunks().at(i).width;
					str = stringf("__expr%d := %s :: %s;", ++line_num, l2.c_str(), l1.c_str());
					f << stringf("%s\n", str.c_str());
					l1=stringf("__expr%d", line_num);
					w1+=w2;
				}
				output_type = true;
				l = stringf("__expr%d", line_num);
			}
			sig_ref[s] = std::make_pair(l, output_type);
		}
		else
		{
			l = it->second.first;
			output_type = it->second.second;
		}
		
		if (expected_width != s.size())
		{
			log(" - changing width of sigspec\n");
			//TODO: this block may not be needed anymore, due to explicit type conversion by "splice" command
			if(!output_type) {
				str = stringf("__expr%d := word1(%s);", ++line_num, l.c_str());
				f << stringf("%s\n", str.c_str());
				l = stringf("__expr%d", line_num);
			} 
			str = stringf ("__expr%d := resize(%s, %d); --sigspec", ++line_num, l.c_str(), expected_width);
			f << stringf("%s\n", str.c_str());
			l = stringf("__expr%d", line_num);
		}
		log_assert(!l.empty());
		if (expected_width == 1 && !bv && output_type) {
			str = stringf ("__expr%d := bool(%s);", ++line_num, l.c_str());
			f << stringf("%s\n", str.c_str());
			l = stringf("__expr%d", line_num);
			output_type = false;
		}
		if (expected_width == 1 && bv && !output_type) {
			str = stringf ("__expr%d := word1(%s);", ++line_num, l.c_str());
			f << stringf("%s\n", str.c_str());
			l = stringf("__expr%d", line_num);
			output_type = true;
		}
		return l;
	}
	
	std::string dump_cell(bool& output_type, const RTLIL::Cell* cell, bool context) {
		auto it = expr_ref.find(cell->name);
		if(it==std::end(expr_ref))
		{
			curr_cell = cell->name;
			//unary cells
			if(cell->type == "$assert") {
				log("writing assert cell - %s\n", cstr(cell->type));
				const RTLIL::SigSpec* expr = &cell->getPort(RTLIL::IdString("\\A"));
				const RTLIL::SigSpec* en = &cell->getPort(RTLIL::IdString("\\EN"));
				log_assert(expr->size() == 1);
				log_assert(en->size() == 1);
				bool t1, t2;
				std::string expr_expr = dump_sigspec(t1, expr, 1, false);
				std::string en_expr = dump_sigspec(t2, en, 1, false);
				str = stringf("__expr%d := %s -> %s;", ++line_num, en_expr.c_str(), expr_expr.c_str());
				f << stringf("%s\n", str.c_str());
				output_type = false;
				expr_ref[cell->name] = std::make_pair(stringf("__expr%d", line_num), output_type);
			}
			else if (cell->type == "$not" || cell->type == "$neg" || cell->type == "$pos" || 
				 cell->type ==  "$reduce_and" || cell->type == "$reduce_or" || cell->type == "$reduce_xor" ||
				 cell->type == "$reduce_bool" || cell->type == "$reduce_xnor" || cell->type == "$logic_not")
			{
				log("writing unary cell - %s\n", cstr(cell->type));
				bool t1;
				int w = cell->parameters.at(RTLIL::IdString("\\A_WIDTH")).as_int();
				int output_width = cell->parameters.at(RTLIL::IdString("\\Y_WIDTH")).as_int();
				std::string l = dump_sigspec(t1, &cell->getPort(RTLIL::IdString("\\A")), w, context);
				std::string cell_expr;
				bool resize = false;
				if(cell->type == "$not" || cell->type == "$neg" || cell->type == "$pos")
				{
					log_assert(!(cell->type == "$neg" || cell->type == "$pos") || context);//should be bv context
					++line_num;
					str = stringf ("__expr%d := %s %s;", line_num, cell_type_translation.at(cell->type.str()).c_str(), l.c_str());
					f << stringf("%s\n", str.c_str());
					/*if (!context && cell->type == "$not") {
					  ++line_num;
					  str = stringf("__expr%d := bool(__expr%d);", line_num, line_num - 1);
					  f << stringf("%s\n", str.c_str());
					  }*/
					cell_expr = stringf("__expr%d", line_num);
				}
				else
				{
					if (cell->type == "$reduce_and")
					{
						str = stringf("__expr%d := ! 0ud%d_0;", ++line_num, w);
						f << stringf("%s\n", str.c_str());
						++line_num;
						str = stringf("__expr%d := __expr%d = %s;", line_num, line_num - 1, l.c_str());
						f << stringf("%s\n", str.c_str());
					}
					else if (cell->type == "$reduce_or" || cell->type == "$reduce_bool")
					{
						str = stringf("__expr%d := 0ud%d_1 >= %s;", ++line_num, w, l.c_str());
						f << stringf("%s\n", str.c_str());
					}
					else if (cell->type == "$logic_not")
					{
						if (w>1)
						{
							str = stringf("__expr%d := 0ud%d_1 >= %s;", ++line_num, w, l.c_str());
							f << stringf("%s\n", str.c_str());
							++line_num;
							str = stringf("__expr%d := ! __expr%d; -- logic not", line_num, line_num -1);
							f << stringf("%s\n", str.c_str());
						}
						else
						{
							str = stringf("__expr%d := ! %s; -- logic not", ++line_num, l.c_str());
							f << stringf("%s\n", str.c_str());
						}
					}
					else if (cell->type == "$reduce_xor" || cell->type == "$reduce_xnor")
					{
						std::string t = (cell->type == "$reduce_xor") ? cell_type_translation.at("$xor") : cell_type_translation.at("$xnor");
						log_assert(w>1);
						int i = w-1;
						++line_num;
						str = stringf("__expr%d := %s[%d:%d]; --reduce", line_num, l.c_str(), i, i);
						f << stringf("%s\n", str.c_str());
						for(--i; i >= 0; --i)
						{
							++line_num;
							str = stringf("__expr%d := %s[%d:%d]; --reduce", line_num, l.c_str(), i, i);
							f << stringf("%s\n", str.c_str());
							++line_num;
							str = stringf("__expr%d := __expr%d %s __expr%d;", line_num, line_num - 1, t.c_str(), line_num - 2);
							f << stringf("%s\n", str.c_str());			  
						}
					}
					cell_expr = stringf("__expr%d", line_num);
				}
				/*if(context && !t1) 
				  {
				  log_assert(w == 1);
				  str = stringf ("__expr%d := word1(%s);", ++line_num, cell_expr.c_str());
				  f << stringf("%s\n", str.c_str());
				  }
				  cell_expr = stringf("__expr%d", line_num);
			      
				  if(output_width != w && context) 
				  {
				  str = stringf ("__expr%d := resize(%s, %d);", ++line_num, cell_expr.c_str(), w);
				  f << stringf("%s\n", str.c_str());
				  cell_expr = stringf("__expr%d", line_num);		  
				  }*/
				if (cell->type =="$not" || cell->type == "%neg" || cell->type == "pos")
					output_type = context;
				else 
					output_type = false;
				expr_ref[cell->name]=std::make_pair(cell_expr, output_type);
			}
			//binary logical cells
			else if (cell->type == "$and" || cell->type == "$or" || cell->type == "$xor" || cell->type == "$xnor" ||
				 cell->type == "$lt" || cell->type == "$le" || cell->type == "$eq" || cell->type == "$ne" ||
				 cell->type == "$eqx" || cell->type == "$nex" || cell->type == "$ge" || cell->type == "$gt" ||
				 cell->type == "$add" || cell->type == "$sub" || cell->type == "$mul" || cell->type == "$div" ||
				 cell->type == "$mod")
			{
				log("writing binary cell - %s\n", cstr(cell->type));
				bool t1, t2;
				int output_width = cell->parameters.at(RTLIL::IdString("\\Y_WIDTH")).as_int();
				log_assert(!(cell->type == "$eq" || cell->type == "$ne" || cell->type == "$eqx" || cell->type == "$nex" ||
					     cell->type == "$ge" || cell->type == "$gt") || output_width == 1);
				bool l1_signed = cell->parameters.at(RTLIL::IdString("\\A_SIGNED")).as_bool();
				bool l2_signed YS_ATTRIBUTE(unused) = cell->parameters.at(RTLIL::IdString("\\B_SIGNED")).as_bool();
				int l1_width = cell->parameters.at(RTLIL::IdString("\\A_WIDTH")).as_int();
				int l2_width = cell->parameters.at(RTLIL::IdString("\\B_WIDTH")).as_int();
	    
				log_assert(l1_signed == l2_signed);
				l1_width = l1_width > output_width ? l1_width : output_width;
				l1_width = l1_width > l2_width ? l1_width : l2_width;
				l2_width = l2_width > l1_width ? l2_width : l1_width;

				bool rel_op = (cell->type == "$lt" || cell->type == "$le" || cell->type == "$eq" || cell->type == "$ne" ||
					       cell->type == "$eqx" || cell->type == "$nex" || cell->type == "$ge" || cell->type == "$gt") 
					? true : false;

				std::string l1 = dump_sigspec(t1, &cell->getPort(RTLIL::IdString("\\A")), l1_width, rel_op ? true : context);
				std::string l2 = dump_sigspec(t2, &cell->getPort(RTLIL::IdString("\\B")), l2_width, rel_op ? true : context);
	    
				++line_num;
				std::string op = cell_type_translation.at(cell->type.str());
	    
				str = stringf ("__expr%d := %s %s %s; --binary operators %d %d", line_num, l1.c_str(), op.c_str(), l2.c_str(),
					       l1_width, l2_width);
				f << stringf("%s\n", str.c_str());

				/*
				  if(cell->type == "$and" || cell->type == "$or" || cell->type == "$xor" || cell->type == "$xnor") 
				  {
				  if(context && !t1) 
				  {
				  log_assert(l1_width == 1);
				  str = stringf ("__expr%d := word1(%s);", ++line_num, l1.c_str());
				  f << stringf("%s\n", str.c_str());
				  l1 = stringf("__expr%d", line_num);
				  }
				  if(context && !t2) 
				  {
				  log_assert(l2_width == 1);
				  str = stringf ("__expr%d := word1(%s);", ++line_num, l2.c_str());
				  f << stringf("%s\n", str.c_str());
				  l2 = stringf("__expr%d", line_num);
				  }
		  
				  if(!context && t1) 
				  {
				  log_assert(l1_width == 1);
				  str = stringf ("__expr%d := bool(%s);", ++line_num, l1.c_str());
				  f << stringf("%s\n", str.c_str());
				  l1 = stringf("__expr%d", line_num);
				  }
				  if(!context && t2) 
				  {
				  log_assert(l2_width == 1);
				  str = stringf ("__expr%d := bool(%s);", ++line_num, l2.c_str());
				  f << stringf("%s\n", str.c_str());
				  l2 = stringf("__expr%d", line_num);
				  }
				  }
				*/
				//resize if the operator is not relational
				if(!rel_op && context && output_width != l1_width)
				{
					++line_num;
					str = stringf ("__expr%d := resize(__expr%d, %d);", line_num, line_num - 1, output_width);
					f << stringf("%s\n", str.c_str());
				}
				if(cell->type == "$and" || cell->type == "$or" || cell->type == "$xor" || cell->type == "$xnor")
					output_type = context;
				else if(rel_op)
					output_type = false;
				else
					output_type = true;
				expr_ref[cell->name] = std::make_pair(stringf("__expr%d", line_num), output_type);
			}
			else if (cell->type == "$shr" || cell->type == "$shl" || cell->type == "$sshr" || cell->type == "$sshl" ||
				 cell->type == "$shift" || cell->type == "$shiftx")
			{
				log("writing binary cell - %s\n", cstr(cell->type));
				log_assert(context);
				bool t1, t2;
				int output_width = cell->parameters.at(RTLIL::IdString("\\Y_WIDTH")).as_int();
				int l1_width = cell->parameters.at(RTLIL::IdString("\\A_WIDTH")).as_int();
				int l2_width = cell->parameters.at(RTLIL::IdString("\\B_WIDTH")).as_int();
				std::string l1 = dump_sigspec(t1, &cell->getPort(RTLIL::IdString("\\A")), l1_width, context);
				std::string l2 = dump_sigspec(t2, &cell->getPort(RTLIL::IdString("\\B")), l2_width, context);
				++line_num;
				str = stringf ("__expr%d := %s %s %s;", line_num, l1.c_str(), cell_type_translation.at(cell->type.str()).c_str(), l2.c_str());
				f << stringf("%s\n", str.c_str());
	    
				if(output_width != l1_width)
				{
					++line_num;
					str = stringf ("__expr%d := resize(__expr%d, %d);", line_num, line_num - 1, output_width);
					f << stringf("%s\n", str.c_str());
				}
				if(cell->type == "$and" || cell->type == "$or" || cell->type == "$xor" || cell->type == "$xnor")
					output_type = context;
				else if(cell->type == "$lt" || cell->type == "$le" || cell->type == "$eq" || cell->type == "$ne" ||
					cell->type == "$eqx" || cell->type == "$nex" || cell->type == "$ge" || cell->type == "$gt")
					output_type = false;
				else 
					output_type = true;
				expr_ref[cell->name] = std::make_pair(stringf("__expr%d", line_num), output_type);
			}
			else if (cell->type == "$logic_and" || cell->type == "$logic_or")
			{
				log("writing binary cell - %s\n", cstr(cell->type));
				log_assert(!context);
				bool t1, t2;
				int output_width = cell->parameters.at(RTLIL::IdString("\\Y_WIDTH")).as_int();
				std::string l1 = dump_sigspec(t1, &cell->getPort(RTLIL::IdString("\\A")), output_width, context);
				std::string l2 = dump_sigspec(t2, &cell->getPort(RTLIL::IdString("\\B")), output_width, context);
				int l1_width = cell->parameters.at(RTLIL::IdString("\\A_WIDTH")).as_int();
				int l2_width = cell->parameters.at(RTLIL::IdString("\\B_WIDTH")).as_int();
				if(l1_width >1)
				{
					str = stringf("__expr%d := 0ud%d_1 >= %s;", ++line_num, l1_width, l1.c_str());
					f << stringf("%s\n", str.c_str());
					l1 = stringf("__expr%d", line_num);
				}
				if(l2_width > 1)
				{
					str = stringf("__expr%d := 0ud%d_1 >= %s;", ++line_num, l2_width, l2.c_str());
					f << stringf("%s\n", str.c_str());
					l2 = stringf("__expr%d", line_num);
				}
				/*if(t1) 
				  {
				  log_assert(output_width == 1);
				  str = stringf("__expr%d := bool(%s);" , ++line_num, l1.c_str());
				  f << stringf("%s\n", str.c_str());
				  l1 = stringf("__expr%d", line_num);
				  }
				  if(t2) 
				  {
				  log_assert(output_width == 1);
				  str = stringf("__expr%d := bool(%s);" , ++line_num, l2.c_str());
				  f << stringf("%s\n", str.c_str());
				  l2 = stringf("__expr%d", line_num);
				  }*/
				if(cell->type == "$logic_and")
				{
					str = stringf ("__expr%d := %s %s %s; -- logic and", ++line_num, l1.c_str(), cell_type_translation.at("$and").c_str(), l2.c_str());
				}
				else if(cell->type == "$logic_or")
				{
					str = stringf ("__expr%d := %s %s %s;", ++line_num, l1.c_str(), cell_type_translation.at("$or").c_str(), l2.c_str());
				}
				f << stringf("%s\n", str.c_str());
				output_type = false;
				expr_ref[cell->name]=std::make_pair(stringf("__expr%d", line_num), output_type);
			}
			//multiplexers
			else if (cell->type == "$mux")
			{
				log("writing mux cell\n");
				int output_width = cell->parameters.at(RTLIL::IdString("\\WIDTH")).as_int();
				bool t1, t2, ts;
				std::string l1 = dump_sigspec(t1, &cell->getPort(RTLIL::IdString("\\A")), output_width, context);
				std::string l2 = dump_sigspec(t2, &cell->getPort(RTLIL::IdString("\\B")), output_width, context);
				std::string s = dump_sigspec(ts, &cell->getPort(RTLIL::IdString("\\S")), 1, false);
				log_assert(!ts);
				log_assert(!s.empty() && !l1.empty() && !l2.empty());
				if(context && !t1)
				{
					log_assert(output_width == 1);
					str = stringf ("__expr%d := word1(%s);", ++line_num, l1.c_str());
					f << stringf("%s\n", str.c_str());
					l1 = stringf("__expr%d", line_num);
				}
				if(context && !t2)
				{
					log_assert(output_width == 1);
					str = stringf ("__expr%d := word1(%s);", ++line_num, l2.c_str());
					f << stringf("%s\n", str.c_str());
					l2 = stringf("__expr%d", line_num);
				}

				if(!context && t1)
				{
					log_assert(output_width == 1);
					str = stringf ("__expr%d := bool(%s);", ++line_num, l1.c_str());
					f << stringf("%s\n", str.c_str());
					l1 = stringf("__expr%d", line_num);
				}
				if(!context && t2)
				{
					log_assert(output_width == 1);
					str = stringf ("__expr%d := bool(%s);", ++line_num, l2.c_str());
					f << stringf("%s\n", str.c_str());
					l2 = stringf("__expr%d", line_num);
				}
		
				++line_num;
				str = stringf ("__expr%d := (%s ? %s : %s); -- mux cell", 
					       line_num, s.c_str(), l2.c_str(), l1.c_str());
				//if s is 0 then l1, if s is 1 then l2 //according to the implementation of mux cell
				f << stringf("%s\n", str.c_str());
				output_type = context;
				expr_ref[cell->name]=std::make_pair(stringf("__expr%d", line_num), output_type);
			}
			else if (cell->type ==  "$pmux")
			{
				log("writing pmux cell\n");
				bool t1, t2, ts;
				int output_width = cell->parameters.at(RTLIL::IdString("\\WIDTH")).as_int();
				int select_width = cell->parameters.at(RTLIL::IdString("\\S_WIDTH")).as_int();
				std::string default_case = dump_sigspec(t1, &cell->getPort(RTLIL::IdString("\\A")), output_width, context);
				std::string cases = dump_sigspec(t2, &cell->getPort(RTLIL::IdString("\\B")), output_width*select_width, context);
				std::string select = dump_sigspec(ts, &cell->getPort(RTLIL::IdString("\\S")), select_width, true);
				int *c = new int[select_width];
            
				for (int i=0; i<select_width; ++i)
				{
					++line_num;
					str = stringf ("__expr%d := %s[%d:%d]; --pmux", line_num, select.c_str(), i, i);
					f << stringf("%s\n", str.c_str());
					c[i] = line_num;
					++line_num;
					if(!context)
					{
						log_assert(output_width == 1);
						str = stringf ("__expr%d := bool(%s[%d:%d]); --pmux", line_num, cases.c_str(), i*output_width+output_width-1,
							       i*output_width);
					}
					else 
						str = stringf ("__expr%d := %s[%d:%d]; --pmux", line_num, cases.c_str(), i*output_width+output_width-1,
							       i*output_width);
					f << stringf("%s\n", str.c_str());
				}
	    
				++line_num;
				str = stringf ("__expr%d := (case bool(__expr%d) : __expr%d; TRUE: %s; esac);", line_num, c[select_width-1], c[select_width-1]+1, default_case.c_str());
				f << stringf("%s\n", str.c_str());
            
				for (int i=select_width-2; i>=0; --i)
				{
					++line_num;
					str = stringf ("__expr%d := (case bool(__expr%d) : __expr%d; TRUE: __expr%d; esac);", line_num, c[i], c[i]+1, line_num-1);
					f << stringf("%s\n", str.c_str());
				}
		
				/*if(!context) 
				  {
				  if(output_width > 1) 
				  {
				  ++line_num;
				  str = stringf("__expr%d := reszie(__expr%d, %d);", line_num, line_num - 1, 1);
				  f << stringf("%s\n", str.c_str());
				  }
				  ++line_num;
				  str = stringf("__expr%d := bool(__expr%d);", line_num, line_num - 1);
				  f << stringf("%s\n", str.c_str());
				  }*/
				output_type = context;
				expr_ref[cell->name]=std::make_pair(stringf("__expr%d", line_num), output_type);
			}
			//registers
			else if (cell->type == "$dff" || cell->type == "$adff" || cell->type == "$dffsr" || cell->type == "$dlatch")
			{
				//TODO: remodelling fo adff cells
				log("writing cell - %s\n", cstr(cell->type));
				bool t1, t2;
				int output_width = cell->parameters.at(RTLIL::IdString("\\WIDTH")).as_int();
				context = output_width > 1 ? true : false;
				log(" - width is %d\n", output_width);
				//$dlatch has enable signal instead of clock
				std::string cond = cell->type == "$dlatch" ? dump_sigspec(t1, &cell->getPort(RTLIL::IdString("\\EN")), 1, false) : 
					dump_sigspec(t1, &cell->getPort(RTLIL::IdString("\\CLK")), 1, false);
				bool polarity = cell->type == "$dlatch" ? cell->parameters.at(RTLIL::IdString("\\EN_POLARITY")).as_bool() :
					cell->parameters.at(RTLIL::IdString("\\CLK_POLARITY")).as_bool();
				const RTLIL::SigSpec* cell_output = &cell->getPort(RTLIL::IdString("\\Q"));
				std::string value = dump_sigspec(t2, &cell->getPort(RTLIL::IdString("\\D")), output_width, context);
				unsigned start_bit = 0;
				for(unsigned i=0; i<cell_output->chunks().size(); ++i)
				{
					output_width = cell_output->chunks().at(i).width;
					log_assert( output_width == cell_output->chunks().at(i).wire->width);//full reg is given the next value
					std::string reg = dump_wire(output_type, cell_output->chunks().at(i).wire, !is_bool_wire(cell_output->chunks().at(i).wire));//register
					std::string slice = value;
					if(cell_output->chunks().size()>1)
					{
						start_bit+=output_width;
						slice = stringf("__expr%d", ++line_num);
						str = stringf ("__expr%d := %s[%d:%d]; --dff", line_num, value.c_str(), start_bit-1, 
							       start_bit-output_width);
						f << stringf("%s\n", str.c_str());
					}
					if(output_width == 1 && t2)
					{
						str = stringf("__expr%d := bool(%s);", ++line_num, slice.c_str()); 
						f << stringf("%s\n", str.c_str());
						slice = stringf("__expr%d", line_num);
					}
					if(cell->type == "$dffsr")
					{
						bool t3, t4;
						std::string sync_reset = dump_sigspec(t3, &cell->getPort(RTLIL::IdString("\\CLR")), 1, false);
						bool sync_reset_pol = cell->parameters.at(RTLIL::IdString("\\CLR_POLARITY")).as_bool();
						std::string sync_reset_value = dump_sigspec(t4, &cell->getPort(RTLIL::IdString("\\SET")),
											    output_width, !is_bool_wire(cell_output->chunks().at(i).wire));
						bool sync_reset_value_pol = cell->parameters.at(RTLIL::IdString("\\SET_POLARITY")).as_bool();
						str = stringf("__expr%d := %s %s;", ++line_num, sync_reset_pol ? "":"!", sync_reset.c_str());
						f << stringf("%s\n", str.c_str());
						str = stringf("__expr%d := %s %s;", ++line_num, sync_reset_value_pol ? "":"!", sync_reset_value.c_str());
						f << stringf("%s\n", str.c_str());
						++line_num;
						str = stringf("__expr%d := __expr%d ? __expr%d : %s;", line_num, line_num - 2, line_num - 1, slice.c_str());
						f << stringf("%s\n", str.c_str());
						slice = stringf("__expr%d", line_num);
					}
					str = stringf("__expr%d := %s %s;", ++line_num, polarity ? "":"!", cond.c_str());
					f << stringf("%s\n", str.c_str());
					++line_num;
					str = stringf("__expr%d := __expr%d ? %s : %s;", line_num, line_num - 1, slice.c_str(), reg.c_str());
					f << stringf("%s\n", str.c_str());
					std::string next = stringf("__expr%d",line_num);
	      
					if(cell->type == "$adff")
					{
						bool t5;
						std::string async_reset = dump_sigspec(t5, &cell->getPort(RTLIL::IdString("\\ARST")), 1, false);
						bool async_reset_pol = cell->parameters.at(RTLIL::IdString("\\ARST_POLARITY")).as_bool();
						std::string async_reset_value = dump_const(&cell->parameters.at(RTLIL::IdString("\\ARST_VALUE")),
											   output_width, 0);
						str = stringf("__expr%d := %s %s;", ++line_num, async_reset_pol ? "":"!", async_reset.c_str());
						f << stringf("%s\n", str.c_str());
						++line_num;
						str = stringf("__expr%d := __expr%d ? %s : %s;", line_num, line_num - 1, async_reset_value.c_str(), next.c_str());
						f << stringf("%s\n", str.c_str());
					}
					str = stringf("__expr%d := next(%s) = %s;", ++line_num, reg.c_str(), next.c_str());
					f << stringf("%s\n", str.c_str());
				}
				output_type = false;
				expr_ref[cell->name]=std::make_pair(stringf("__expr%d",line_num), output_type);
			}
			//memories
			else if (cell->type == "$meminit")
			{
				log("writing meminit cell\n");
				str = cell->parameters.at(RTLIL::IdString("\\MEMID")).decode_string();
				std::string mem = cstr(module->memories.at(RTLIL::IdString(str.c_str()))->name);
				int address_width = cell->parameters.at(RTLIL::IdString("\\ABITS")).as_int();
				int elem_width = cell->parameters.at(RTLIL::IdString("\\WIDTH")).as_int();
				bool t1, t2;
				std::string address = dump_sigspec(t1, &cell->getPort(RTLIL::IdString("\\ADDR")), address_width, true);
				std::string data = dump_sigspec(t1, &cell->getPort(RTLIL::IdString("\\DATA")), elem_width, true);
				str = stringf("__expr%d := READ(%s, %s) = %s;", ++line_num, mem.c_str(), address.c_str(), data.c_str());
				f << stringf("%s\n", str.c_str());
				output_type = true;
				expr_ref[cell->name]=std::make_pair(stringf("__expr%d",line_num), output_type);
			}
			else if (cell->type == "$memrd")
			{
				log("writing memrd cell\n");
				if (cell->parameters.at("\\CLK_ENABLE").as_bool() == true)
					log_error("The smv backend does not support $memrd cells with built-in registers. Run memory_dff with -wr_only.\n");
				str = cell->parameters.at(RTLIL::IdString("\\MEMID")).decode_string();
				std::string mem = cstr(module->memories.at(RTLIL::IdString(str.c_str()))->name);
				int address_width = cell->parameters.at(RTLIL::IdString("\\ABITS")).as_int();
				bool t1;
				std::string address = dump_sigspec(t1, &cell->getPort(RTLIL::IdString("\\ADDR")), address_width, true);
				str = stringf("__expr%d := READ(%s, %s);", ++line_num, mem.c_str(), address.c_str());
				f << stringf("%s\n", str.c_str());
				output_type = true;
				expr_ref[cell->name]=std::make_pair(stringf("__expr%d",line_num), output_type);
			}
			else if (cell->type == "$memwr")
			{
				log("writing memwr cell\n");
				bool t1, t2, t3, t4;
				if (cell->parameters.at("\\CLK_ENABLE").as_bool() == false)
					log_error("The smv backen does not support $memwr cells without built-in registers. Run memory_dff (but with -wr_only).\n");
				std::string clk = dump_sigspec(t1, &cell->getPort(RTLIL::IdString("\\CLK")), 1, false);
				bool polarity = cell->parameters.at(RTLIL::IdString("\\CLK_POLARITY")).as_bool();
				std::string enable = dump_sigspec(t2, &cell->getPort(RTLIL::IdString("\\EN")), 1, false);
				int address_width = cell->parameters.at(RTLIL::IdString("\\ABITS")).as_int();
				std::string address = dump_sigspec(t3, &cell->getPort(RTLIL::IdString("\\ADDR")), address_width, true);
				int data_width = cell->parameters.at(RTLIL::IdString("\\WIDTH")).as_int();
				std::string data = dump_sigspec(t4, &cell->getPort(RTLIL::IdString("\\DATA")), data_width, context);
				str = cell->parameters.at(RTLIL::IdString("\\MEMID")).decode_string();
				std::string mem = cstr(module->memories.at(RTLIL::IdString(str.c_str()))->name);
				str = stringf("__expr%d := %s %s;", ++line_num, polarity ? "":"!", clk.c_str());
				f << stringf("%s\n", str.c_str());
				++line_num;
				str = stringf("__expr%d := __expr%d & %s;", line_num, line_num - 1, enable.c_str());
				f << stringf("%s\n", str.c_str());
				str = stringf("__expr%d := WRITE(%s, %s, %s);", ++line_num, mem.c_str(), address.c_str(), data.c_str());
				f << stringf("%s\n", str.c_str());
				mem_next[mem].insert(std::make_pair(line_num-1, line_num));
				output_type = context;
			}
			else if (cell->type == "$slice")
			{
				log("writing slice cell\n");
				bool t1;
				const RTLIL::SigSpec* input = &cell->getPort(RTLIL::IdString("\\A"));
				int input_width = cell->parameters.at(RTLIL::IdString("\\A_WIDTH")).as_int();
				log_assert(input->size() == input_width);
				std::string input_line = dump_sigspec(t1, input, input_width, true);
				log_assert(t1);
				int output_width = cell->parameters.at(RTLIL::IdString("\\Y_WIDTH")).as_int();
				int offset = cell->parameters.at(RTLIL::IdString("\\OFFSET")).as_int();
				str = stringf("__expr%d := %s[%d:%d]; --slice", ++line_num, input_line.c_str(), output_width+offset-1, offset);
				f << stringf("%s\n", str.c_str());
				output_type = true;
				expr_ref[cell->name]=std::make_pair(stringf("__expr%d",line_num), output_type);
			}
			else if (cell->type == "$concat")
			{
				log("writing concat cell\n");
				//		log_assert(context);
				bool t1, t2;
				const RTLIL::SigSpec* input_a = &cell->getPort(RTLIL::IdString("\\A"));
				int input_a_width = cell->parameters.at(RTLIL::IdString("\\A_WIDTH")).as_int();
				log_assert(input_a->size() == input_a_width);
				std::string input_a_line = dump_sigspec(t1, input_a, input_a_width, true);
				const RTLIL::SigSpec* input_b = &cell->getPort(RTLIL::IdString("\\B"));
				int input_b_width = cell->parameters.at(RTLIL::IdString("\\B_WIDTH")).as_int();
				log_assert(input_b->size() == input_b_width);
				std::string input_b_line = dump_sigspec(t2, input_b, input_b_width, true);
				if(!t1)
				{
					log_assert(input_a_width == 1);
					str = stringf ("__expr%d := word1(%s);", ++line_num, input_a_line.c_str());
					f << stringf("%s\n", str.c_str());
					input_a_line = stringf("__expr%d", line_num);
				}
				if(!t2)
				{
					log_assert(input_b_width == 1);
					str = stringf ("__expr%d := word1(%s);", ++line_num, input_b_line.c_str());
					f << stringf("%s\n", str.c_str());
					input_b_line = stringf("__expr%d", line_num);
				}
		
				str = stringf("__expr%d := %s :: %s;", ++line_num, input_a_line.c_str(), input_b_line.c_str());
				f << stringf("%s\n", str.c_str());
				output_type = true;
				expr_ref[cell->name]=std::make_pair(stringf("__expr%d",line_num), output_type);
			}
			else
			{
				log_error("Unsupport cell type : %s\n", cell->type.c_str());
			}
			curr_cell.clear();
			return expr_ref[cell->name].first;
		}
		else
		{
			output_type = it->second.second;
			return it->second.first;
		}
	}

	std::string dump_property(RTLIL::Wire *wire) {
		bool type;
		std::string l = dump_wire(type, wire, false);
		return l;
	}

	void dump() {
		f << stringf("MODULE main\n");
		
		log("creating intermediate wires map\n");
		//creating map of intermediate wires as output of some cell
		for (auto it = module->cells_.begin(); it != module->cells_.end(); ++it)
		{
			RTLIL::Cell *cell = it->second;
			const RTLIL::SigSpec* output_sig = get_cell_output(cell);
			if(output_sig==nullptr)
				continue;
			RTLIL::SigSpec s = sigmap(*output_sig);
			output_sig = &s;
			log(" - %s\n", cstr(cell->name));
			if (cell->type == "$memrd")
			{
				for(unsigned i=0; i<output_sig->chunks().size(); ++i)
				{
					RTLIL::Wire *w = output_sig->chunks().at(i).wire;
					RTLIL::IdString wire_id = w->name;
					inter_wire_map[wire_id].insert(WireInfo(cell->name,&output_sig->chunks().at(i)));
				}
			}
			else if(cell->type == "$memwr" || cell->type == "$meminit")
			{
				continue;//nothing to do
			}
			else if(cell->type == "$dff" || cell->type == "$adff" || cell->type == "$dffsr" || cell->type == "$dlatch")
			{
				RTLIL::IdString wire_id = output_sig->chunks().front().wire->name;
				for(unsigned i=0; i<output_sig->chunks().size(); ++i)
				{
					RTLIL::Wire *w = output_sig->chunks().at(i).wire;
					RTLIL::IdString wire_id = w->name;
					inter_wire_map[wire_id].insert(WireInfo(cell->name,&output_sig->chunks().at(i)));
					basic_wires[wire_id] = true;
				}
			}
			else 
			{
				for(unsigned i=0; i<output_sig->chunks().size(); ++i)
				{
					RTLIL::Wire *w = output_sig->chunks().at(i).wire;
					RTLIL::IdString wire_id = w->name;
					inter_wire_map[wire_id].insert(WireInfo(cell->name,&output_sig->chunks().at(i)));
				}
			}
		}
		
		log("writing input\n");
		std::map<int, RTLIL::Wire*> inputs, outputs;
		
		for (auto &wire_it : module->wires_) 
		{
			RTLIL::Wire *wire = wire_it.second;
			if (wire->port_input)
				inputs[wire->port_id] = wire;
			if (wire->port_output)
			{
				outputs[wire->port_id] = wire;
			}
		}

		log("writing IVAR\n");
		f << stringf("\nIVAR\n");
		for (auto &it : inputs) 
		{
			RTLIL::Wire *wire = it.second;
			dump_basic_wire(wire);
			//			basic_wires[wire->name] = false;
		}

		log("writing VAR\n");
		f << string("\nVAR\n");
		for (auto &wire_it : module->wires_) 
		{
			RTLIL::Wire *w = wire_it.second;
			if(basic_wires[w->name] && !w->port_input )
			{
				dump_basic_wire(w);
			}
		}
		  
		log("writing arrays\n");
		for(auto mem_it = module->memories.begin(); mem_it != module->memories.end(); ++mem_it)
		{
			dump_memory(mem_it->second);
		}
		
		log("writing DEFINE\n");
		f << string("\nDEFINE\n");
		log("writing INIT\n");
		int init_start_line_num = line_num + 1;
		for (auto wire : module->wires())
			if (basic_wires[wire->name]  && !wire->port_input && wire->attributes.count("\\init"))
			{
				Const val = wire->attributes.at("\\init");
				val.bits.resize(wire->width);
				++line_num;
				if (wire->width > 1)
				{
					str = stringf("__expr%d := %s = 0ub%d_%s; -- %s", line_num, expr_ref[wire->name].first.c_str(), wire->width, val.as_string().c_str(), cstr(wire->name));
				}
				else
				{
					bool tval = val.as_bool();
					str = stringf("__expr%d := %s %s; -- %s", line_num, tval ? "" : "!", expr_ref[wire->name].first.c_str(), cstr(wire->name) );
				}
				f << stringf("%s\n", str.c_str());
			}

		//memory initialization
		for(auto cell_it = module->cells_.begin(); cell_it != module->cells_.end(); ++cell_it)
		{
			RTLIL::Cell *cell = cell_it->second;
			if(cell->type == "$meminit")
			{
				bool output_type;
				str = dump_cell(output_type, cell_it->second, true);                                             
			}
		}

		
		int init_end_line_num = line_num;
		for (int i=init_start_line_num; i < init_end_line_num; ++i)
		{
			str = stringf("__expr%d := __expr%d & __expr%d;", ++line_num, i, i+1);
			f << stringf("%s\n", str.c_str());
		}
		std::string init_expr;
		if (line_num > 0)
			init_expr = stringf("__expr%d", line_num);
		else
			init_expr = stringf("TRUE");
		
		//registers next
		//memory next
		log("collecting TRANS - registers\n");
		std::vector<std::string> trans_expr_list;
		for(auto cell_it = module->cells_.begin(); cell_it != module->cells_.end(); ++cell_it)
		{
			RTLIL::Cell *cell = cell_it->second;
			if(cell->type == "$dff" || cell->type == "$adff" || cell->type == "$dffsr" || cell->type == "$dlatch" || 
			   cell->type == "$memwr")
			{
				bool output_type;
				str = dump_cell(output_type, cell_it->second, true);                                             
				if(cell->type != "$memwr")
					trans_expr_list.push_back(str);
			}
		}

		log("collecting TRANS - memories\n");
		for(auto mem_it = module->memories.begin(); mem_it != module->memories.end(); ++mem_it)
		{
			str = dump_memory_next(mem_it->second);
			if (!str.empty())
				trans_expr_list.push_back(str);
		}		

		log("writing TRANS -- list size %d\n", trans_expr_list.size());
		for(unsigned long i=0; i+1 < trans_expr_list.size(); ++i)
		{
			str = stringf("__expr%d := %s & %s;", ++line_num, trans_expr_list[i].c_str(), trans_expr_list[i+1].c_str());
			f << stringf("%s\n", str.c_str());
		}

		std::string trans_expr = trans_expr_list.size() == 0 ? stringf("TRUE") : stringf("__expr%d", line_num);

		
		log("writing INVARSPEC\n");
		std::vector<std::string> invar_list;
		for (auto it = module->cells_.begin(); it != module->cells_.end(); ++it)
		{
			RTLIL::Cell *cell = it->second;
			if (cell->type == "$assert")
			{
				bool t1;
				str = dump_cell(t1, cell, false);
				invar_list.push_back(str);
			}
		}

		f << stringf("\n");
		//writing init_expr
		f << stringf("INIT %s;\n", init_expr.c_str());
		//writing trans_expr
		f << stringf("TRANS %s;\n", trans_expr.c_str());
		//writing invars
		for(unsigned long i=0; i < invar_list.size(); ++i)
		{
			f << stringf("INVARSPEC %s;\n", invar_list[i].c_str());
                }

		f << stringf("\n");
	}

	static void dump(std::ostream &f, RTLIL::Module *module, RTLIL::Design *design, SmvDumperConfig &config) {
		SmvDumper dumper(f, module, design, &config);
		dumper.dump();
	}
};

struct SmvBackend : public Backend
{
	SmvBackend() : Backend("smv", "write design to SMV file") { }
	
	virtual void help() {
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_smv [filename]\n");
		log("\n");
		log("Write the current design to an SMV file.\n");
	}

	virtual void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) {
		std::string top_module_name;
		std::string buf_type, buf_in, buf_out;
		std::string true_type, true_out;
		std::string false_type, false_out;
		SmvDumperConfig config;

		log_header("Executing SMV backend.\n");

		size_t argidx=1;
		extra_args(f, filename, args, argidx);
		
		if (top_module_name.empty())
			for (auto & mod_it:design->modules_)
				if (mod_it.second->get_bool_attribute("\\top"))
					top_module_name = mod_it.first.str();

		*f << stringf("-- Generated by %s\n", yosys_version_str);
		*f << stringf("--  %s developed and maintained by Clifford Wolf <clifford@clifford.at>\n", yosys_version_str);
		*f << stringf("-- SMV Backend developed by Ahmed Irfan <irfan@fbk.eu> - Fondazione Bruno Kessler, Trento, Italy\n");
		*f << stringf("------------------------------------------------------------------------------------------------\n");
		
		std::vector<RTLIL::Module*> mod_list;

		for (auto module_it : design->modules_)
		{
			RTLIL::Module *module = module_it.second;
			if (module->get_bool_attribute("\\blackbox"))
				continue;

			if (module->processes.size() != 0)
				log_error("Found unmapped processes in module %s: unmapped processes are not supported in SMV backend!\n", RTLIL::id2cstr(module->name));

			if (module->name == RTLIL::escape_id(top_module_name))
			{
				SmvDumper::dump(*f, module, design, config);
				top_module_name.clear();
				continue;
			}

			mod_list.push_back(module);
		}

		if (!top_module_name.empty())
			log_error("Can't find top module `%s'!\n", top_module_name.c_str());

		for (auto module : mod_list)
			SmvDumper::dump(*f, module, design, config);
	}
} SmvBackend;

PRIVATE_NAMESPACE_END
