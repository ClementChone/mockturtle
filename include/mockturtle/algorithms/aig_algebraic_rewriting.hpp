/*!
  \file aig_algebraic_rewriting.hpp
  \brief AIG algebraric rewriting

  EPFL CS-472 2021 Final Project Option 1
*/

#pragma once

#include "../networks/aig.hpp"
#include "../views/depth_view.hpp"
#include "../views/topo_view.hpp"

#include <vector>
namespace mockturtle
{

namespace detail
{

template<class Ntk>
class aig_algebraic_rewriting_impl
{
  using node = typename Ntk::node;
  using signal = typename Ntk::signal;

public:
  aig_algebraic_rewriting_impl( Ntk& ntk )
    : ntk( ntk )
  {
    static_assert( has_level_v<Ntk>, "Ntk does not implement depth interface." );
  }

  void run()
  {
    bool cont{true}; /* continue trying */
    while ( cont )
    {
      cont = false; /* break the loop if no updates can be made */
      ntk.foreach_gate( [&]( node n ){
        if ( try_algebraic_rules( n ) )
        {
          ntk.update_levels();
          cont = true;
        }
      });
    }
  }

private:
  /* Try various algebraic rules on node n. Return true if the network is updated. */
  bool try_algebraic_rules( node n )
  {
    if ( try_associativity( n ) )
      return true;
    if ( try_distributivity( n ) )
      return true;
    /* TODO: add more rules here... */
    if ( try_3_layer_distributivity( n ))
      return true;

    return false;
  }
/* ======================================================================================================================= */

void update_associativity(signal a, signal b, signal c, node n)
{
  signal g1_output ;
  signal g0_output ;
  g1_output = ntk.create_and( a, b );
  g0_output = ntk.create_and( c, g1_output);
  ntk.substitute_node(n, g0_output);
  ntk.update_levels();
}

  /* Try the associativity rule on node n. Return true if the network is updated. */
  bool try_associativity( node n )
  {
    /* TODO */
    std::vector<signal> fan_in ;
    ntk.foreach_fanin( n, [&] (auto const& sig) {
      fan_in.push_back(sig) ;
    });

    if ( ntk.is_pi(ntk.get_node(fan_in[0])) && ntk.is_pi(ntk.get_node(fan_in[1])))  //  PI
      { return false;}

    if ( ntk.is_on_critical_path(n) )
      {
        node g0 = ntk.get_node(fan_in[0]); //gate 0
        node g1 = ntk.get_node(fan_in[1]); // gate 1

        std::vector<signal> fan_in_g0 ;
        std::vector<signal> fan_in_g1 ;

        ntk.foreach_fanin( g0, [&] (auto const& sig) {
          fan_in_g0.push_back(sig) ;
        });

        ntk.foreach_fanin( g1, [&] (auto const& sig) {
          fan_in_g1.push_back(sig) ;
        });

        if ( ntk.level(g0) > ntk.level(g1) + 1 && !ntk.is_complemented(fan_in[0]) )   //g0 on critical path and the transformation is ok
          {
            if (ntk.is_on_critical_path(ntk.get_node(fan_in_g0[0])) && ntk.is_on_critical_path(ntk.get_node(fan_in_g0[1])))
            return false;

            if (ntk.is_on_critical_path(ntk.get_node(fan_in_g0[0])))
            {
              update_associativity(fan_in_g0[1], fan_in[1], fan_in_g0[0], n);
              return true;
            }
            else                                     // g0.children[1] is the critical path
            {
              update_associativity(fan_in_g0[0], fan_in[1], fan_in_g0[1], n);
              return true;
            }
          }
        else if ( ntk.level(g1) > ntk.level(g0)+1 && !ntk.is_complemented(fan_in[1])) //g1 on critical path and the transformation is ok
        {
          if (ntk.is_on_critical_path(ntk.get_node(fan_in_g1[0])) && ntk.is_on_critical_path(ntk.get_node(fan_in_g1[1])))
          return false;

          if (ntk.is_on_critical_path(ntk.get_node(fan_in_g1[0]))) //g1.children[0] is the critical path
          {
            update_associativity(fan_in_g1[1], fan_in[0], fan_in_g1[0], n);
            return true;
          }
          else                                     // g1.children[1] is the critical path
          {
            update_associativity(fan_in_g1[0], fan_in[0], fan_in_g1[1], n);
            return true;
          }
        }
        else
        {return false;}   //transformation not valid
      }
    else
      {return false;}   // gate is not on the critical path
  }

void update_distributivity(signal a, signal b, signal distributed, node g0)

{
  signal g1_output = ntk.create_or(a, b);
  signal g0_output = ntk.create_nand(distributed, g1_output);
  ntk.substitute_node(g0, g0_output);
}

void update_3_distributivity(signal gg_crit, signal gg_not_crit, signal g_not_crit, signal child_not_crit, node n)
{
  signal a = ntk.create_and(gg_not_crit, child_not_crit);
  signal b = ntk.create_and(gg_crit, a);
  signal c = ntk.create_and(!g_not_crit, child_not_crit);
  signal f = ntk.create_and( !b, !c );
  ntk.substitute_node(n, !f);
}

  bool is_fanins_complemented(node n)
   {
     std::vector<signal> fan_in ;
     ntk.foreach_fanin( n, [&] (auto const& sig) {
       fan_in.push_back(sig) ;
     });
     return ntk.is_complemented(fan_in[0]) && ntk.is_complemented(fan_in[1]) ;
   }


  /* Try the distributivity rule on node n. Return true if the network is updated. */
  bool try_distributivity( node n )
  {
    /* TODO */
    if (!ntk.is_on_critical_path(n) )
    {return false;}

    std::vector<signal> fan_in ;
    ntk.foreach_fanin( n, [&] (auto const& sig) {
      fan_in.push_back(sig) ;
    });

    if (fan_in.size() < 2)
    return false;

    node g0 = ntk.get_node(fan_in[0]); //gate g0
    node g1 = ntk.get_node(fan_in[1]); //gate g1

    if (! (ntk.is_on_critical_path(g0) && ntk.is_on_critical_path(g1)))
      return false;

    if ( ntk.level(n) >= 2  && is_fanins_complemented(n) )
    {
        // Access of the different nodes and fan_in involve
        std::vector<signal> fan_in_g0 ; // fan_in of g0

        ntk.foreach_fanin( g0, [&] (auto const& sig) {
          fan_in_g0.push_back(sig) ;
        });

        if (fan_in_g0.size() < 2)
        return false;

        std::vector<signal> fan_in_g1 ; // fan_in of g1

        ntk.foreach_fanin( g1, [&] (auto const& sig) {
          fan_in_g1.push_back(sig) ;
        });

        if (fan_in_g1.size() < 2)
        return false;

          if ( ntk.get_node(fan_in_g0[0]) == ntk.get_node(fan_in_g1[0]) && ntk.is_complemented(fan_in_g0[0]) == ntk.is_complemented(fan_in_g1[0]) )
          { if (ntk.is_on_critical_path(ntk.get_node(fan_in_g0[1])) || ntk.is_on_critical_path(ntk.get_node(fan_in_g1[1])))
            return false;

            update_distributivity(fan_in_g0[1], fan_in_g1[1], fan_in_g0[0], n);
            return true ;
          }

          else if ( ntk.get_node(fan_in_g0[0]) == ntk.get_node(fan_in_g1[1]) && ntk.is_complemented(fan_in_g0[0]) == ntk.is_complemented(fan_in_g1[1]) )
          { if (ntk.is_on_critical_path(ntk.get_node(fan_in_g0[1])) || ntk.is_on_critical_path(ntk.get_node(fan_in_g1[0])))
            return false;

            update_distributivity(fan_in_g0[1], fan_in_g1[0], fan_in_g0[0], n);
            return true ;
          }

          else if ( ntk.get_node(fan_in_g0[1]) == ntk.get_node(fan_in_g1[0]) && ntk.is_complemented(fan_in_g0[1]) == ntk.is_complemented(fan_in_g1[0]) )
          { if (ntk.is_on_critical_path(ntk.get_node(fan_in_g0[0])) || ntk.is_on_critical_path(ntk.get_node(fan_in_g1[1])))
            return false;

            update_distributivity(fan_in_g0[0], fan_in_g1[1], fan_in_g0[1], n);
            return true ;
          }

          else if ( ntk.get_node(fan_in_g0[1]) == ntk.get_node(fan_in_g1[1]) && ntk.is_complemented(fan_in_g0[1]) == ntk.is_complemented(fan_in_g1[1]) )
          { if (ntk.is_on_critical_path(ntk.get_node(fan_in_g0[0])) || ntk.is_on_critical_path(ntk.get_node(fan_in_g1[0])))
            return false;

            update_distributivity(fan_in_g0[0], fan_in_g1[0], fan_in_g0[1], n);
            return true ;
          }
        }
    return false; //no distributivity possible
  }


bool try_3_layer_distributivity( node n )
{
  if (!ntk.is_on_critical_path(n) )
  {return false;}
  else
  {
    std::vector<signal> child ;
    ntk.foreach_fanin( n, [&] (auto const& sig) {
      child.push_back(sig) ;
    });

    node child0 = ntk.get_node(child[0]);
    node child1 = ntk.get_node(child[1]);
    signal child0_s = child[0];
    signal child1_s = child[1];  //signal menant a child 1

    if (ntk.level(child0) < ntk.level(child1))  //critical path on the left side
    {
      std::swap( child0, child1);
      std::swap( child0_s, child1_s);
    }

    if (ntk.level(child1) + 2 >= ntk.level(child0)) //not worth
    { return false;}

    if (!ntk.is_complemented(child0_s)) //if not complemented, no distributivity
    {return false;}

    std::vector<signal> g_child ;
    ntk.foreach_fanin( child0, [&] (auto const& sig) {
      g_child.push_back(sig) ;
    });

    node g_child0 = ntk.get_node(g_child[0]);
    node g_child1 = ntk.get_node(g_child[1]);
    signal g_child0_s = g_child[0];
    signal g_child1_s = g_child[1];

    if (ntk.level(g_child0) < ntk.level(g_child1))  //critical path on the left side
    {
      std::swap( g_child0, g_child1);
      std::swap( g_child0_s, g_child1_s);
    }

    if (ntk.is_on_critical_path(g_child0) && ntk.is_on_critical_path(g_child1) ) //if both critical, not worth
    {return false;}

    if (!ntk.is_complemented(g_child0_s)) //if not complemented, no distributivity
    {return false;}

    std::vector<signal> gg_child ;
    ntk.foreach_fanin( g_child0, [&] (auto const& sig) {
      gg_child.push_back(sig) ;
    });

    node gg_child0 = ntk.get_node(gg_child[0]);
    node gg_child1 = ntk.get_node(gg_child[1]);
    signal gg_child0_s = gg_child[0];
    signal gg_child1_s = gg_child[1];

    if (ntk.level(gg_child0) < ntk.level(gg_child1))  //critical path on the left side
    {
      std::swap( gg_child0, gg_child1);
      std::swap( gg_child0_s, gg_child1_s);
    }

    if (ntk.is_on_critical_path(gg_child0) && ntk.is_on_critical_path(gg_child1) ) //if both critical, not worth
    {return false;}
    //do the change
    update_3_distributivity(gg_child0_s, gg_child1_s, g_child1_s, child1_s, n);
    return true;
}
}

private:
  Ntk& ntk;
};

} // namespace detail

/* Entry point for users to call */
template<class Ntk>
void aig_algebraic_rewriting( Ntk& ntk )
{
  static_assert( std::is_same_v<typename Ntk::base_type, aig_network>, "Ntk is not an AIG" );

  depth_view dntk{ntk};
  detail::aig_algebraic_rewriting_impl p( dntk );
  p.run();
}

} /* namespace mockturtle */
