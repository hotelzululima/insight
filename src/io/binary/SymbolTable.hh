#ifndef SYMBOLTABLE_HH
# define SYMBOLTABLE_HH

# include <string>
# include <kernel/Architecture.hh>
# include <utils/Object.hh>
# include <tr1/unordered_map>

class SymbolTable : public Object  
{
public:
  typedef std::tr1::unordered_map<std::string, address_t> SymbolMap;
  typedef SymbolMap::const_iterator const_symbol_iterator;
  typedef std::tr1::unordered_map<address_t, std::string> AddressMap;
  typedef AddressMap::const_iterator const_address_iterator;

  SymbolTable ();
  virtual ~SymbolTable ();

  virtual SymbolTable *clone () const;
  virtual size_t size () const;
  virtual bool empty () const;
  virtual void add_symbol (const std::string &id, address_t a);
  virtual void merge_with (const SymbolTable *table);
    
  virtual bool has (const std::string &id) const; 
  virtual bool has (address_t a) const;
  virtual address_t get (const std::string &id) const; 
  virtual const std::string &get (address_t a) const;
  virtual void output_text (std::ostream &out) const;
  virtual const_address_iterator find (address_t a) const;
  virtual const_symbol_iterator find (const std::string &id) const;

  virtual const_symbol_iterator begin_symbols () const;
  virtual const_symbol_iterator end_symbols () const;
  virtual const_address_iterator begin_addresses () const;
  virtual const_address_iterator end_addresses () const;

protected:
  SymbolMap symbmap;
  AddressMap addrmap;
};

#endif /* ! SYMBOLTABLE_HH */
