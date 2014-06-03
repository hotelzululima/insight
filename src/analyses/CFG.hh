#ifndef ANALYSES_CFG_HH
# define ANALYSES_CFG_HH

# include <map>
# include <string>
# include <utils/graph.hh>
# include <kernel/Microcode.hh>

class CFG_BasicBlock
{
public:
  virtual ~CFG_BasicBlock () {}
  virtual bool operator == (const CFG_BasicBlock &e) const = 0;
  virtual std::string pp () const = 0;
  virtual MicrocodeNode *get_entry () const = 0;
  virtual MicrocodeNode *get_exit () const = 0;
};

class CFG_Edge
{
public:
  virtual ~CFG_Edge () {}
  virtual bool operator == (const CFG_Edge &e) const = 0;
  virtual std::string pp () const = 0;
  virtual CFG_BasicBlock *get_src () const = 0;
  virtual CFG_BasicBlock *get_tgt () const = 0;
};

struct CFG_NodeStore
{
  typedef std::vector<CFG_BasicBlock *> store_type;
  typedef store_type::iterator node_iterator;
  typedef store_type::const_iterator const_node_iterator;
};

class CFG : public GraphInterface<CFG_BasicBlock, CFG_Edge, CFG_NodeStore>
{
protected:
  CFG ();

public:
  virtual ~CFG();

  static CFG *createFromMicrocode (const Microcode *prog,
				   const MicrocodeAddress &start);

  typedef CFG_BasicBlock node_type;
  typedef CFG_Edge edge_type;

  virtual const_node_iterator begin_nodes () const;
  virtual const_node_iterator end_nodes () const;
  virtual node_iterator begin_nodes ();
  virtual node_iterator end_nodes ();

  virtual node_type *get_entry_point () const;
  virtual std::string get_label_node (node_type *n) const;
  virtual std::pair<edge_type *, node_type *>
  get_first_successor (node_type *n) const;
  virtual std::pair<edge_type *, node_type *>
  get_next_successor (node_type *n, edge_type *e) const;
  virtual node_type *get_source (edge_type *e) const;
  virtual node_type *get_target (edge_type *e) const;
  virtual void output_text(std::ostream & out) const;

  virtual node_type *new_node (MicrocodeNode *entry);
  virtual void add_edge (node_type *src, node_type *tgt);

private:
  store_type nodes;
  std::map<MicrocodeNode *, CFG_BasicBlock *> node2bb;
  node_type *entrypoint;
};

#endif /* ! ANALYSES_CFG_HH */
