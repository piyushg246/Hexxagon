/* Author : Piyush Goyal */

// associate barriers according to initial(input board state) difference in pieces: havent tried yet
// depth getting smaller in the middlegame: futility/null-move pruning to be added
// history heuristic isn't producing successfull results: need to make some changes, maybe killer heuristic can be used instead
// opening book/database can be made although already decent depth is reached in opening

#include <iostream>
using namespace std;
#include <malloc.h>
#include <set>
#include <stack>
#include <time.h>
#include <vector>
#include <deque>
#include <stdio.h>
#include <iso646.h>
#include <algorithm>
 
double a_heur_cons = 0.02, b_heur_cons = 0.04, c_heur_cons = 0.06;
 
//#include <bits/stdc++.h>
//void binary_code(unsigned long long int);
typedef pair<int, int> PR;
typedef unsigned long long int ulll;
ulll HASH_VALUE_PER_PIECE[6][7][3];
 
ulll turn_HASHVAL;
 
ulll print_input_hashval;
 
bool ORDER_decider=false;
 
set< PR > NEIGHBOUR[6][7];
set< PR > DIST2NEIGHBOUR[6][7];
bool kya_yaar=false;
int MAX_DEPTH ;
int int_MAX = 9999999;
int int_MIN = -9999999;
const int max_size=420;
int parent_x, parent_y;
int temp_parent_x,temp_parent_y;
int ans_x, ans_y;
int temp_x, temp_y;
int DEPTH=1;
int MAX_BRANCH;
clock_t start;
enum Color {NONE=0, RED = 1, BLUE = 2};
Color PLAYER_COLOR, OPP_COLOR;
int INCRE;
int ans_value=0;
 
int total_nodes=0;
int hash_found=0;
double ratio=0;
 
ulll M = 3000017;
bool available[3000017];
int subtree_depth[3000017];
int minmax_value[3000017];
PR bestmove_parent[3000017];
PR bestmove[3000017];
int bestmove_type[3000017];
bool DONE_1[3000017];
bool zeromoves[3000017];
int type[3000017];
// ulll M2 = 2013169;
// bool available2[2013169];
// int subtree_depth2[2013169];
// int minmax_value2[2013169];
// PR bestmove2[2013169];
// PR bestmove2_parent[2013169];
// int bestmove2_type[2013169];
 
ulll id1[3000017];
//ulll id2[2013169];
 
// bool cuttoff_defined[25][2];
// int killer_TYPE[25][2];
// PR killer_move[25][2];
// PR killer_parent[25][2];
// int killer_cutoffs[25][2];
// int cutoffs_for_spread[25][6][7];
// int cutoffs_for_jump[25][6][7][6][7];
 
bool OPENING=false;
bool MIDGAME=false;
bool ENDGAME=false;
 
ulll my_HISTORY_saver[6][7][6][7];
ulll opp_HISTORY_saver[6][7][6][7];
 
 
 
// double max_ratio=int_MIN;
// double min_ratio=int_MAX;
// double temp_max_ratio;
// double temp_min_ratio;
// bool max_GREATER=false;
// bool min_LESS=false;
 
struct struct_for_sorting
{
    PR move;
    PR parent;
    int move_type;
    int heuristic_val;
    ulll history;
};
 
bool struct_compare(struct_for_sorting a, struct_for_sorting b)
{ 
    return a.heuristic_val>b.heuristic_val;
}
 
bool history_compare(struct_for_sorting a, struct_for_sorting b)
{ 
    
    //return (a.move_type==0 && b.move_type==1) || a.history>b.history;
    if(a.history==b.history)
        return a.heuristic_val>b.heuristic_val;
    else
    return a.history>b.history;
    
}
 
class Stone{
public:
 
    Color c;
 
public:
 
    Stone(){
        c = NONE;
    }
 
 
    Stone(Stone *obj){
        c = (*obj).c;
    }
 
    Stone(Color c1){
        c = c1;
    }
 
};
 
 
class Board{
public:
 
    Stone arr[6][7];
    int red_count;
    int blue_count;
 
public:
 
    Board(){
        for(int i=0;i<6;i++){
            for(int j=0;j<7;j++){
                arr[i][j] = Stone(NONE);
            }
        }
        red_count=blue_count=0;
    }
 
    Board(Board *obj){
        for(int i=0;i<6;i++){
            for(int j=0;j<7;j++){
                arr[i][j] = Stone(&((*obj).arr[i][j]));
            }
        }
        red_count=obj->red_count;
        blue_count=obj->blue_count;
    }
 
    int spread(Color clr, int x, int y, ulll *hashval2)
    {
        arr[x][y].c = clr;
        ulll hashval = *hashval2;
        hashval = (hashval^HASH_VALUE_PER_PIECE[x][y][0]);
        if(clr==RED)
        {
            hashval ^= HASH_VALUE_PER_PIECE[x][y][1];
        }
        else
        {
            hashval ^= HASH_VALUE_PER_PIECE[x][y][2];
        }
        if(clr==RED)red_count++;
        else blue_count++;
        Color opp = clr==RED?BLUE:RED;
        set<PR>::iterator si;
        for(si=NEIGHBOUR[x][y].begin();si!=NEIGHBOUR[x][y].end();si++)
        {
            if(arr[(*si).first][(*si).second].c==opp)
            {
                arr[(*si).first][(*si).second].c=clr; 
                hashval ^= HASH_VALUE_PER_PIECE[(*si).first][(*si).second][2];
                hashval ^= HASH_VALUE_PER_PIECE[(*si).first][(*si).second][1];       
                if(clr==BLUE)
                {
                    blue_count++;
                    red_count--;
                }
                else
                {
                    red_count++;
                    blue_count--;
                }            
            }            
        }
        *hashval2=hashval;
    }
 
    int jump(Color clr, int a, int b, int x, int y, ulll *hashval2)
    {
        arr[x][y].c = clr;
        arr[a][b].c = NONE;
        ulll hashval = *hashval2;
        hashval ^= HASH_VALUE_PER_PIECE[x][y][0];
        hashval ^= HASH_VALUE_PER_PIECE[a][b][0];
        if(clr==RED)
        {
            hashval ^= HASH_VALUE_PER_PIECE[a][b][1];
            hashval ^= HASH_VALUE_PER_PIECE[x][y][1];
        }
        else
        {
            hashval ^= HASH_VALUE_PER_PIECE[a][b][2];
            hashval ^= HASH_VALUE_PER_PIECE[x][y][2];   
        }
        Color opp = clr==RED?BLUE:RED;
        set<PR>::iterator si;
        for(si=NEIGHBOUR[x][y].begin();si!=NEIGHBOUR[x][y].end();si++)
        {
            if(arr[(*si).first][(*si).second].c==opp)
            {
                arr[(*si).first][(*si).second].c=clr;  
                hashval ^= HASH_VALUE_PER_PIECE[(*si).first][(*si).second][2];
                hashval ^= HASH_VALUE_PER_PIECE[(*si).first][(*si).second][1];
                if(clr==BLUE)
                {
                    blue_count++;
                    red_count--;
                }
                else
                {
                    red_count++;
                    blue_count--;
                }            
            }            
        }
        *hashval2=hashval;
    }
    
    int distinct_spread(PR parent[], PR moves[] , Color clr, int spread_count)
    {
        int dist_count=spread_count;
        int i,j;
        for(i=0;i<6;i++)
        {
            for(j=0;j<7;j++)
            {
                if(arr[i][j].c!=NONE)continue;
                set<PR>::iterator si;
                for(si=NEIGHBOUR[i][j].begin();si!=NEIGHBOUR[i][j].end();si++)
                {
                    int k=(*si).first;
                    int l=(*si).second;
                    if(arr[k][l].c==clr)
                    {
                        moves[dist_count].first=i;
                        moves[dist_count].second=j;
                        parent[dist_count].first=k;
                        parent[dist_count].second=l;
                        dist_count++;
                        break;
                    }
                }
            }
        }
 
        return dist_count;
 
    }
 
    int distinct_jump( PR parent[], PR moves[] , int spread_count, Color clr)
    {
        //set< pair<int, PR> > st;
        Color opp= clr==RED?BLUE:RED;
        int dist_count=spread_count;
        int i,j;
        if(0)
        {
            for(i=0;i<6;i++)
            {
                for(j=0;j<7;j++)
                {
                    //if(dist_count==max_size)return dist_count;
                    if(arr[i][j].c!=NONE)continue;
                    set<PR>::iterator si;
                    // int enemy_there=0;
                    // int total_there=0;
                    // for(si=NEIGHBOUR[i][j].begin();si!=NEIGHBOUR[i][j].end();si++)
                    // {
                    //  total_there++;
                    //  if(arr[(*si).first][(*si).second].c==opp)
                    //  enemy_there++;
                    // }
                    for(si=DIST2NEIGHBOUR[i][j].begin();si!=DIST2NEIGHBOUR[i][j].end();si++)
                    {
                        int k=(*si).first;
                        int l=(*si).second;
                        if(arr[k][l].c!=clr)continue;
                        // set<PR>::iterator si2;
                        // int cnt=0;
                        // bool flag = true;
                        // int x,y;
                        // for(si2=NEIGHBOUR[k][l].begin();si2!=NEIGHBOUR[k][l].end();si2++)
                        // {
                        //     if(arr[(*si2).first][(*si2).second].c==opp)
                        //     {
                        //         cnt++;
                        //         x=(*si2).first;
                        //         y=(*si2).second;
                        //     }
                        //     if(arr[(*si2).first][(*si2).second].c==clr)
                        //     {
                        //         flag=false;
                        //     }
                        // }
                        // if( 1 )
                        // {
                            parent[dist_count].first=k;
                            parent[dist_count].second=l;
                            moves[dist_count].first=i;
                            moves[dist_count].second=j;
                            dist_count++;
                        // }
     
                    }
                }
            }
        }
        else
        {
            for(i=0;i<6;i++)
            {
                for(j=0;j<7;j++)
                {
                    if(dist_count==max_size)return dist_count;
                    if(arr[i][j].c!=clr)continue;
                    set<PR>::iterator si;
                    // int enemy_there=0;
                    // int total_there=0;
                    // for(si=NEIGHBOUR[i][j].begin();si!=NEIGHBOUR[i][j].end();si++)
                    // {
                    //  total_there++;
                    //  if(arr[(*si).first][(*si).second].c==opp)
                    //  enemy_there++;
                    // }
                    for(si=DIST2NEIGHBOUR[i][j].begin();si!=DIST2NEIGHBOUR[i][j].end();si++)
                    {
                        int k=(*si).first;
                        int l=(*si).second;
                        if(arr[k][l].c!=NONE)continue;
                        set<PR>::iterator si2;
                        int cnt=0;
                        // bool flag = true;
                        // int x,y;
                        // for(si2=NEIGHBOUR[k][l].begin();si2!=NEIGHBOUR[k][l].end();si2++)
                        // {
                        //     if(arr[(*si2).first][(*si2).second].c==opp)
                        //     {
                        //         cnt++;
                        //         x=(*si2).first;
                        //         y=(*si2).second;
                        //     }
                        //     if(arr[(*si2).first][(*si2).second].c==clr)
                        //     {
                        //         flag=false;
                        //     }
                        // }
                        // if( 1 )
                        // {
                            parent[dist_count].first=i;
                            parent[dist_count].second=j;
                            moves[dist_count].first=k;
                            moves[dist_count].second=l;
                            dist_count++;
                        // }
     
                    }
                }
            }
        }
        
 
        return dist_count;
 
    }
 
    int distinct_jump4( PR parent[], PR moves[] , int spread_count, Color clr)
   {
       //set< pair<int, PR> > st;
       Color opp= clr==RED?BLUE:RED;
       int dist_count=spread_count;
       int i,j;
       for(i=0;i<6;i++)
       {
           for(j=0;j<7;j++)
           {
               //if(dist_count==60)return dist_count;
               if(arr[i][j].c!=clr)continue;
               set<PR>::iterator si;
               for(si=DIST2NEIGHBOUR[i][j].begin();si!=DIST2NEIGHBOUR[i][j].end();si++)
               {
                   int k=(*si).first;
                   int l=(*si).second;
                   if(arr[k][l].c!=NONE)continue;
                   set<PR>::iterator si2;
                   int cnt=0;
                   bool flag = true;
                   for(si2=NEIGHBOUR[k][l].begin();si2!=NEIGHBOUR[k][l].end();si2++)
                   {
                       if(arr[(*si2).first][(*si2).second].c==opp)
                       {
                           ;//flag=false;
                           //break;
                       }
                       else if(arr[(*si2).first][(*si2).second].c==clr)
                       {
                           flag=false;
                           break;
                       }
                   }
                   if(flag)
                   {
                       parent[dist_count].first=i;
                       parent[dist_count].second=j;
                       moves[dist_count].first=k;
                       moves[dist_count].second=l;
                       dist_count++;
                   }
 
               }
           }
       }
 
       return dist_count;
 
   }
 
   int distinct_jump2( PR parent[], PR moves[] , int spread_count, Color clr)
   {
       //set< pair<int, PR> > st;
       Color opp= clr==RED?BLUE:RED;
       int dist_count=spread_count;
       int i,j;
       for(i=0;i<6;i++)
       {
           for(j=0;j<7;j++)
           {
               //if(dist_count==60)return dist_count;
               if(arr[i][j].c!=clr)continue;
               set<PR>::iterator si;
               for(si=DIST2NEIGHBOUR[i][j].begin();si!=DIST2NEIGHBOUR[i][j].end();si++)
               {
                   int k=(*si).first;
                   int l=(*si).second;
                   if(arr[k][l].c!=NONE)continue;
                   set<PR>::iterator si2;
                   int cnt=0;
                   bool flag = true;
                   for(si2=NEIGHBOUR[k][l].begin();si2!=NEIGHBOUR[k][l].end();si2++)
                   {
                       if(arr[(*si2).first][(*si2).second].c==opp)
                       {
                           flag=false;
                           break;
                       }
                       else if(arr[(*si2).first][(*si2).second].c==clr)
                       {
                           flag=false;
                           break;
                       }
                   }
                   if(!flag)
                   {
                       parent[dist_count].first=i;
                       parent[dist_count].second=j;
                       moves[dist_count].first=k;
                       moves[dist_count].second=l;
                       dist_count++;
                   }
 
               }
           }
       }
 
       return dist_count;
 
   }
 int distinct_jump3( PR parent[], PR moves[] , int spread_count, Color clr)
   {
       //set< pair<int, PR> > st;
       Color opp= clr==RED?BLUE:RED;
       int dist_count=spread_count;
       int i,j;
       for(i=0;i<6;i++)
       {
           for(j=0;j<7;j++)
           {
               //if(dist_count==60)return dist_count;
               if(arr[i][j].c!=clr)continue;
               set<PR>::iterator si;
               // int enemy_there=0;
               // for(si=NEIGHBOUR[i][j].begin();si!=NEIGHBOUR[i][j].end();si++)
               // {
               //      if(arr[(*si).first][(*si).second].c==opp)
               //         {
               //             enemy_there++;
               //         }
               // }
               for(si=DIST2NEIGHBOUR[i][j].begin();si!=DIST2NEIGHBOUR[i][j].end();si++)
               {
                   int k=(*si).first;
                   int l=(*si).second;
                   if(arr[k][l].c!=NONE)continue;
                   set<PR>::iterator si2;
                   int cnt=0;
                   bool flag = true;
                   int buddies_here=0;
                   for(si2=NEIGHBOUR[k][l].begin();si2!=NEIGHBOUR[k][l].end();si2++)
                   {
                       if(arr[(*si2).first][(*si2).second].c==opp)
                       {
                           cnt++;
                       }
                       if(arr[(*si2).first][(*si2).second].c==clr)
                       {
                           flag=false;
                           buddies_here++;
                           //break;
                       }
                   }
                   if( (flag && cnt>0) || cnt>=2)
                   {
                       parent[dist_count].first=i;
                       parent[dist_count].second=j;
                       moves[dist_count].first=k;
                       moves[dist_count].second=l;
                       dist_count++;
                   }
 
               }
           }
       }
 
       return dist_count;
 
   }
 
   int distinct_jump5( PR parent[], PR moves[] , int spread_count, Color clr)
   {
       //set< pair<int, PR> > st;
       Color opp= clr==RED?BLUE:RED;
       int dist_count=spread_count;
       int i,j;
       // int cc= clr==BLUE?blue_count:red_count;
       // int bc= clr==RED?blue_count:red_count;
       // bool cond = (cc<=(42-cc-bc));
       if(1)
       {
           for(i=0;i<6;i++)
           {
               for(j=0;j<7;j++)
               {
                   //if(dist_count==60)return dist_count;
                   if(arr[i][j].c!=clr)continue;
                   set<PR>::iterator si;
                   // int enemy_there=0;
                   // for(si=NEIGHBOUR[i][j].begin();si!=NEIGHBOUR[i][j].end();si++)
                   // {
                   //      if(arr[(*si).first][(*si).second].c==opp)
                   //         {
                   //             enemy_there++;
                   //         }
                   // }
                   for(si=DIST2NEIGHBOUR[i][j].begin();si!=DIST2NEIGHBOUR[i][j].end();si++)
                   {
                       int k=(*si).first;
                       int l=(*si).second;
                       if(arr[k][l].c!=NONE)continue;
                       set<PR>::iterator si2;
                       int cnt=0;
                       bool flag = true;
                       int buddies_here=0;
                       for(si2=NEIGHBOUR[k][l].begin();si2!=NEIGHBOUR[k][l].end();si2++)
                       {
                           if(arr[(*si2).first][(*si2).second].c==opp)
                           {
                               cnt++;
                               break;
                           }
                           // if(arr[(*si2).first][(*si2).second].c==clr)
                           // {
                           //     flag=false;
                           //     buddies_here++;
                           //     //break;
                           // }
                       }
                       if( cnt>0 )
                       {
                           parent[dist_count].first=i;
                           parent[dist_count].second=j;
                           moves[dist_count].first=k;
                           moves[dist_count].second=l;
                           dist_count++;
                       }
     
                   }
               }
           }
       }
       else
       {
           for(i=0;i<6;i++)
           {
               for(j=0;j<7;j++)
               {
                   //if(dist_count==60)return dist_count;
                   if(arr[i][j].c!=NONE)continue;
                   set<PR>::iterator si;
                   int cnt=0;
                   for(si=NEIGHBOUR[i][j].begin();si!=NEIGHBOUR[i][j].end();si++)
                   {
                       if(arr[(*si).first][(*si).second].c==opp)
                       {
                           cnt++;
                           break;
                       }
                       // if(arr[(*si2).first][(*si2).second].c==clr)
                       // {
                       //     flag=false;
                       //     buddies_here++;
                       //     //break;
                       // }
                   }
                   if(cnt==0)continue;
                   // int enemy_there=0;
                   // for(si=NEIGHBOUR[i][j].begin();si!=NEIGHBOUR[i][j].end();si++)
                   // {
                   //      if(arr[(*si).first][(*si).second].c==opp)
                   //         {
                   //             enemy_there++;
                   //         }
                   // }
                   for(si=DIST2NEIGHBOUR[i][j].begin();si!=DIST2NEIGHBOUR[i][j].end();si++)
                   {
                       int k=(*si).first;
                       int l=(*si).second;
                       if(arr[k][l].c!=clr)continue;
                       // set<PR>::iterator si2;
                       // int cnt=0;
                       // bool flag = true;
                       // int buddies_here=0;
                       
                       // if( cnt>0 )
                       // {
                           parent[dist_count].first=k;
                           parent[dist_count].second=l;
                           moves[dist_count].first=i;
                           moves[dist_count].second=j;
                           dist_count++;
                      // }
     
                   }
               }
           }
       }
       
 
       return dist_count;
 
   }
 
    int eval_heur()
    {
        if(PLAYER_COLOR==RED)
        {
            return red_count - blue_count;
        }
        else
            return blue_count - red_count;
    }
  
    // double get_ratio()
    // {
    //     if(PLAYER_COLOR==RED)
    //     {
    //       if(blue_count==0)return 9999;
    //       else
    //         return ((double)red_count)/blue_count;
    //     }
    //     else
    //     {
    //       if(red_count==0)return 9999;
    //       else
    //         return ((double)blue_count)/red_count;
    //     }
 
    // }
 
    // double complex_heur()
    // {
    //     double ans = 0;
    //     ans += (red_count-blue_count);
    //     for(int i=0;i<6;i++)
    //     {
    //         for(int j=0;j<7;j++)
    //         {
    //             if(arr[i][j].c==NONE)continue;
    //             else if(arr[i][j].c==RED)
    //             {
    //                 set<PR>::iterator si;
    //                 int oc=0,pc=0,tc=0;
    //                 for(si=NEIGHBOUR[i][j].begin();si!=NEIGHBOUR[i][j].end();si++)
    //                 {
    //                     Color cl = arr[(*si).first][(*si).second].c;
    //                     if(cl==RED)
    //                     {}
    //                 }
    //             }
    //         }
    //     }
    // }
 
 
};
 
class Treenode{
 
public:
    Board bd;
    bool done;
    int heuristic;
    int type;
    int moves_done;
    ulll hashval;
 
public:
    Treenode(Board *obj, int moves_till_now)
    {
        bd = Board( obj );
        done = false;
        heuristic = bd.eval_heur();
        type=1;
        moves_done=moves_till_now;
        hashval=0;
        for(int i=0;i<6;i++)
        {
            for(int j=0;j<7;j++)
            {
                if(bd.arr[i][j].c==NONE)
                {
                    hashval ^= HASH_VALUE_PER_PIECE[i][j][0];
                }
                else if(bd.arr[i][j].c==RED)
                {
                    hashval ^= HASH_VALUE_PER_PIECE[i][j][1];
                }
                else
                {
                    hashval ^= HASH_VALUE_PER_PIECE[i][j][2];   
                }
            }
        }
        print_input_hashval=hashval;
    }
 
 
    Treenode(Treenode *tr, int a, int b, int x, int y, Color cl, int move_type)
    {
        hashval = tr->hashval;
        hashval^= turn_HASHVAL;
        done = false;
        bd = Board( &(tr->bd) );
        if(move_type==1)
            bd.jump(cl,a,b, x, y, &hashval);
        else
            bd.spread(cl,x,y, &hashval);
        heuristic = bd.eval_heur();
        int xx = heuristic<0?(-heuristic):heuristic;
        int tot_pieces = bd.blue_count + bd.red_count;
        moves_done = tr->moves_done + 1;        
        if(cl==PLAYER_COLOR)
            {
                type=2;
            }
        else 
            {   
                type=1;
            }
        if(bd.red_count==0 || bd.blue_count==0)
        {
            done=true;
            if(heuristic>0)
            {
                heuristic=int_MAX;                
            }
            else if(heuristic<0)
            {
                heuristic=int_MIN;
            }
 
        }                
        else if(moves_done==100)
        {
            done=true;            
            if(heuristic>0)
            {
                heuristic=int_MAX;                
            }
            else if(heuristic<0)
            {
                heuristic=int_MIN;
            }
        }
        else if(bd.red_count+bd.blue_count==42)
        {
            done=true;
            if(heuristic>0)
            {
                heuristic=int_MAX;                
            }
            else if(heuristic<0)
            {
                heuristic=int_MIN;
            }
        }
        else if(OPENING)
        {
            if(tot_pieces<=14)
            {
              if(heuristic>=1 && cl==OPP_COLOR)
              {
                  done=true;
                  heuristic+=5;
              }
              else if(heuristic<=-1 && cl==PLAYER_COLOR)
              {
                  done=true;
                  heuristic-=5;
              }
            }
            else if(tot_pieces<=18)
            {
              if(heuristic>=1 && cl==OPP_COLOR)
              {
                  done=true;
                  heuristic+=5;
              }
              else if(heuristic<=-1 && cl==PLAYER_COLOR)
              {
                  done=true;
                  heuristic-=5;
              }
            }
            // else if(tot_pieces<=16)
            // {
            //   if(heuristic>=2 && cl==OPP_COLOR)
            //   {
            //       done=true;
            //       heuristic=(int_MAX*xx)/(0.00);
            //   }
            //   else if(heuristic<=-2 && cl==PLAYER_COLOR)
            //   {
            //       done=true;
            //       heuristic=(int_MIN*xx)/(0.00);
            //   }
            // }
            else if(tot_pieces<=25)
            {
              if(heuristic>=1 && cl==OPP_COLOR)
              {
                  done=true;
                  heuristic+=6;
              }
              else if(heuristic<=-1 && cl==PLAYER_COLOR)
              {
                  done=true;
                  heuristic-=6;
              }
            }
            else if(tot_pieces<=28)
            {
              if(heuristic>=2 && cl==OPP_COLOR)
              {
                  done=true;
                  heuristic+=6;
              }
              else if(heuristic<=-2 && cl==PLAYER_COLOR)
              {
                  done=true;
                  heuristic-=6;
              }
            }
            else if(tot_pieces<=33)
            {
              if(heuristic>=3 && cl==OPP_COLOR)
              {
                  done=true;
                  heuristic+=6;
              }
              else if(heuristic<=-3 && cl==PLAYER_COLOR)
              {
                  done=true;
                  heuristic-=6;
              }
            }
            else 
            {
              if(heuristic>=3 && cl==OPP_COLOR)
              {
                  done=true;
                  heuristic+=6;
              }
              else if(heuristic<=-3 && cl==PLAYER_COLOR)
              {
                  done=true;
                  heuristic-=6;
              }
            }
            
            // if(heuristic>=1)
            // {
            //     done=true;
            //     heuristic=int_MAX;
            // }
            // else if(heuristic<=-18)
            // {
            //     done=true;
            //     heuristic=int_MIN;
            // }
        }
        else if(MIDGAME)
        {
            if(tot_pieces<=25)
            {
              if(heuristic>=1 && cl==OPP_COLOR)
              {
                  done=true;
                  heuristic+=6;
              }
              else if(heuristic<=-1 && cl==PLAYER_COLOR)
              {
                  done=true;
                  heuristic-=6;
              }
            }
            else if(tot_pieces<=30)
            {
              if(heuristic>=1 && cl==OPP_COLOR)
              {
                  done=true;
                  heuristic+=6;
              }
              else if(heuristic<=-1 && cl==PLAYER_COLOR)
              {
                  done=true;
                  heuristic-=6;
              }
            }
            else if(tot_pieces<=34)
            {
              if(heuristic>=2 && cl==OPP_COLOR)
              {
                  done=true;
                  heuristic+=6;
              }
              else if(heuristic<=-2 && cl==PLAYER_COLOR)
              {
                  done=true;
                  heuristic-=6;
              }
            }
            else if(tot_pieces<=37)
            {
              if(heuristic>=3 && cl==OPP_COLOR)
              {
                  done=true;
                  heuristic+=6;
              }
              else if(heuristic<=-3 && cl==PLAYER_COLOR)
              {
                  done=true;
                  heuristic-=6;
              }
            }
            else
            {
              if(heuristic>=3 && cl==OPP_COLOR)
              {
                  done=true;
                  heuristic+=6;
              }
              else if(heuristic<=-3 && cl==PLAYER_COLOR)
              {
                  done=true;
                  heuristic-=6;
              }
            }
            // if(heuristic>=21)
            // {
            //     done=true;
            //     heuristic=int_MAX;
            // }
            // else if(heuristic<=-21)
            // {
            //     done=true;
            //     heuristic=int_MIN;
            // }
        }
        else if(ENDGAME)
        {
            if(tot_pieces<=35)
            {
                if(heuristic>=3 && cl==OPP_COLOR)
                {
                    done=true;
                    heuristic+=6;
                }
                else if(heuristic<=-3 && cl==PLAYER_COLOR)
                {
                    done=true;
                    heuristic-=6;
                }
            }
            else if(tot_pieces<=37)
            {
                if(heuristic>=3 && cl==OPP_COLOR)
                {
                    done=true;
                    heuristic+=6;
                }
                else if(heuristic<=-3 && cl==PLAYER_COLOR)
                {
                    done=true;
                    heuristic-=6;
                }
            }
            // else if(tot_pieces<=37)
            // {
            //     if(heuristic>=12 && cl==OPP_COLOR)
            //     {
            //         done=true;
            //         heuristic=(int_MAX*xx)/(0.00);
            //     }
            //     else if(heuristic<=-12 && cl==PLAYER_COLOR)
            //     {
            //         done=true;
            //         heuristic=(int_MIN*xx)/(0.00);
            //     }
            // }
 
        }
        
    }
 
    // double get_ratio()
    // {
    //   return bd.get_ratio();
    // }
 
};
 
 
int alphabeta(Treenode* node, int depth, int alpha, int beta){
 
    clock_t curr = clock();
        double d = (double)(curr-start)/(double)CLOCKS_PER_SEC;
        if(d>0.9325)
        {
            cout<<parent_x<<" "<<parent_y<<endl;
            cout<<ans_x<<" "<<ans_y<<endl;
            cout<<DEPTH-1<<endl;
            cout<<hash_found<<" "<<total_nodes<<endl;
            ratio=(double)hash_found/total_nodes;
            cout<<ratio<<endl;
            cout<<ans_value<<endl;
            cout<<kya_yaar<<endl;
            cout<<OPENING<<" "<<MIDGAME<<" "<<ENDGAME<<endl;
            cout<<print_input_hashval<<endl;
            exit(0);
        }
    int i,j;
    
    if(depth<=0 || node->done==true)
    {
        return node->heuristic;
    }
    
 
 
    if(beta<=alpha)
    {   
        if(node->type==1)return alpha;
        else
            return beta;
    }
    total_nodes++;
    PR firstmove ;
    PR firstmove_parent ;
    int firstmove_type ;
 
 
    bool flag=true;
    int ind1= node->hashval%M;
    if(available[ind1]&&id1[ind1]==node->hashval&&type[ind1]==node->type)
    {
        hash_found++;
        if(subtree_depth[ind1]>=depth || zeromoves[ind1] )
        {
            return minmax_value[ind1];
        }
        firstmove_type=bestmove_type[ind1];
        firstmove.first=bestmove[ind1].first;
        firstmove.second=bestmove[ind1].second;
        firstmove_parent.first=bestmove_parent[ind1].first;
        firstmove_parent.second=bestmove_parent[ind1].second;
    }
    else
    {
        flag=false;
    }
 
    if(node->type==1)
    {   
        int max = -99999999;
        PR parent[max_size+1];
        PR moves[max_size+1];
        int types[max_size+1];
        int spread_count=0;
        if(flag)
        {
            parent[0].first = firstmove_parent.first;
            parent[0].second = firstmove_parent.second;
            moves[0].first=firstmove.first;
            moves[0].second=firstmove.second;
            types[0]=firstmove_type;
            spread_count++;
        }
        spread_count = node->bd.distinct_spread(parent,moves,PLAYER_COLOR,spread_count);
        for(int tempp=flag?1:0;tempp<spread_count;tempp++)
        {
            types[tempp]=0;
        }
        // int dist_moves=node->bd.distinct_jump(parent,moves,spread_count,PLAYER_COLOR);
        // if(dist_moves<=2)
        // {
        //     dist_moves=node->bd.distinct_jump2(parent,moves,spread_count,PLAYER_COLOR);
        //     if(dist_moves>=10)dist_moves=10;
        // }
        // else if(node->bd.red_count+node->bd.blue_count>=35)
        // {
        //     dist_moves=node->bd.distinct_jump2(parent,moves,spread_count,PLAYER_COLOR);   
        // }
        // if(node->bd.red_count+node->bd.blue_count>=39)
        // {
        //     dist_moves=node->bd.distinct_jump3(parent,moves,spread_count,PLAYER_COLOR);   
        // }
        // if(dist_moves==0)
        // {
        //     dist_moves=node->bd.distinct_jump3(parent,moves,spread_count,PLAYER_COLOR);   
        //     if(dist_moves>=5)dist_moves=5;
        // }
        int dist_moves;
 
        if(DEPTH-depth==0)
        {
            if(OPENING)
            {
                dist_moves=node->bd.distinct_jump3(parent,moves,spread_count,PLAYER_COLOR);
            }
            else if(MIDGAME)
            {
                dist_moves=node->bd.distinct_jump3(parent,moves,spread_count,PLAYER_COLOR); 
            }
            else
            dist_moves=node->bd.distinct_jump(parent,moves,spread_count,PLAYER_COLOR);
        }
 
        else if(OPENING)
        {
            dist_moves=node->bd.distinct_jump3(parent,moves,spread_count,PLAYER_COLOR);
            
        }
        else if(MIDGAME)
        {
            dist_moves=node->bd.distinct_jump3(parent,moves,spread_count,PLAYER_COLOR);
        }
        else
        {
            if(node->bd.red_count+node->bd.blue_count<=38)
            {
               dist_moves=node->bd.distinct_jump5(parent,moves,spread_count,PLAYER_COLOR);   
            }
            else
            dist_moves=node->bd.distinct_jump(parent,moves,spread_count,PLAYER_COLOR);   
 
        }
        if(dist_moves>50)kya_yaar=true;
        // if(dist_moves==0)
        // {
        //     dist_moves=node->bd.distinct_jump2(parent,moves,dist_moves,PLAYER_COLOR);
        // }
        // if(node->bd.blue_count+node->bd.red_count>=40)
        // {
        //     dist_moves=node->bd.distinct_jump3(parent,moves,spread_count,PLAYER_COLOR);
        // }
        // if(dist_moves==0)
        // {
        //     dist_moves=node->bd.distinct_jump3(parent,moves,spread_count,PLAYER_COLOR);   
        // }
        
 
        // if((dist_moves<=2&&node->bd.red_count+node->bd.blue_count>=30)|| node->bd.red_count+node->bd.blue_count>=36 || node->moves_done>=95)
        // {
        //     dist_moves=node->bd.distinct_jump(parent,moves,spread_count,PLAYER_COLOR);
        // }
        
        // if( (node->heuristic>=9 && spread_count>=3 && tot_pieces<=36) || (node->heuristic>=10 && spread_count>=2 && tot_pieces<=37) )
        // {
        //     return int_MAX;            
        // }
 
        if(dist_moves==0)
        {
            int ans;
            if(node->heuristic<0)ans=int_MIN;
            else if(node->heuristic>0)ans=int_MAX;
            else ans=0;
            available[ind1]=true;
            minmax_value[ind1]=ans;
            subtree_depth[ind1]=depth;
            zeromoves[ind1]=true;
            id1[ind1]=node->hashval;
            type[ind1]=node->type;
            return ans;
        }
 
        clock_t curr2 = clock();
        double d2 = (double)(curr2-start)/(double)CLOCKS_PER_SEC;
        if(d2>0.93)
        {
            cout<<parent_x<<" "<<parent_y<<endl;
            cout<<ans_x<<" "<<ans_y<<endl;
            cout<<DEPTH-1<<endl;
            cout<<hash_found<<" "<<total_nodes<<endl;
            ratio=(double)hash_found/total_nodes;
            cout<<ratio<<endl;
            cout<<ans_value<<endl;
            cout<<kya_yaar<<endl;
            cout<<OPENING<<" "<<MIDGAME<<" "<<ENDGAME<<endl;
            cout<<print_input_hashval<<endl;
            exit(0);
        }
 
        for(int tempp=spread_count;tempp<dist_moves;tempp++)
        {
            types[tempp]=1;
        }
        int index=0;
        int required_type=0;
        int c_killer=0;
        int strt = flag?1:0;
        int move_no = DEPTH-depth;
        int total_pieces = node->bd.red_count+node->bd.blue_count;
        int breaker=dist_moves;
        
 
        if(depth==1)
        {
            // for(int ix=0;ix<dist_moves;ix++)
            // {
            //     int opp_pieces = (OPP_COLOR==RED)?node->bd.red_count:node->bd.blue_count;
            //     int my_pieces = (PLAYER_COLOR==RED)?node->bd.red_count:node->bd.blue_count;
            //     int added=0;
            //     set<PR>::iterator si;
            //     for(si=NEIGHBOUR[moves[ix].first][moves[ix].second].begin();si!=NEIGHBOUR[moves[ix].first][moves[ix].second].end();si++)
            //     {
            //         if(node->bd.arr[(*si).first][(*si).second].c==OPP_COLOR)
            //         {
            //             opp_pieces--;
            //             my_pieces++;
            //         }            
            //     }
            //     if(types[ix]==0)my_pieces++;
            //     int temp = my_pieces- opp_pieces;
 
            // }
 
                //if(dist_moves>80 && !ENDGAME)dist_moves=80;
            for(int ix = 0 ; ix< dist_moves; ix++)
            {   
                i = moves[ix].first;
                j = moves[ix].second;
                int k = parent[ix].first;
                int l = parent[ix].second;
                int move_type=types[ix];
                int opp_pieces = (OPP_COLOR==RED)?node->bd.red_count:node->bd.blue_count;
                int my_pieces = (PLAYER_COLOR==RED)?node->bd.red_count:node->bd.blue_count;
                //int added=0;
                set<PR>::iterator si;
                for(si=NEIGHBOUR[moves[ix].first][moves[ix].second].begin();si!=NEIGHBOUR[moves[ix].first][moves[ix].second].end();si++)
                {
                    if(node->bd.arr[(*si).first][(*si).second].c==OPP_COLOR)
                    {
                        opp_pieces--;
                        my_pieces++;
                    }            
                }
                if(types[ix]==0)my_pieces++;
                int temp = my_pieces- opp_pieces;
                if(opp_pieces==0){ temp=int_MAX; }
                if(temp>max || (temp==max && (!ORDER_decider)))
                {   
                    max=temp;
                    required_type=move_type;
                    index=ix;
                    if(max>alpha)
                    {   alpha=max;
                        if(depth==DEPTH)
                        {
                            temp_x = i;
                            temp_y = j;
                            temp_parent_x=k;
                            temp_parent_y=l;       
     
                        }
                    }
                    if(beta<=alpha)
                        {
                            //do updation of table
                            if(available[ind1]==false || (available[ind1] && subtree_depth[ind1]<=depth) )
                            {
                                available[ind1]=true;
                                minmax_value[ind1]=alpha;
                                subtree_depth[ind1]=depth;
         
                                bestmove_parent[ind1].first=parent[ix].first;
                                bestmove_parent[ind1].second=parent[ix].second;
                                bestmove[ind1].first=moves[ix].first;
                                bestmove[ind1].second=moves[ix].second;
                                bestmove_type[ind1]=move_type;
                                id1[ind1]=node->hashval;
                                type[ind1]=node->type;
                                zeromoves[ind1]=false;
                                if(alpha==int_MIN || alpha==int_MAX)
                                {
                                    DONE_1[ind1]=true;
                                }
                                else
                                {
                                    DONE_1[ind1]=false;
                                }
                            }
     
                            // if(move_type==0)
                            // {
                            //     set<PR>::iterator si;
                            //     for(si=NEIGHBOUR[i][j].begin();si!=NEIGHBOUR[i][j].end();si++)
                            //     {
                            //         int ax,ay;
                            //         ax=(*si).first;
                            //         ay=(*si).second;
                            //         if(node->bd.arr[ax][ay].c==PLAYER_COLOR)
                            //         {
                            //             my_HISTORY_saver[i][j][ax][ay] += (1<<depth) ;
                            //         }
                            //     }
                            // }
                            // else
                            // {
                            //     my_HISTORY_saver[i][j][k][l] += (1<<depth) ;
                            // }
     
                            return alpha;
                        }
                }
     
     
            }   
            //do updation of table
            int ix=index;
            //do updation of table
            available[ind1]=true;
            minmax_value[ind1]=alpha;
            subtree_depth[ind1]=depth;
     
            bestmove_parent[ind1].first=parent[ix].first;
            bestmove_parent[ind1].second=parent[ix].second;
            bestmove[ind1].first=moves[ix].first;
            bestmove[ind1].second=moves[ix].second;
            bestmove_type[ind1]=required_type;
            id1[ind1]=node->hashval;
            zeromoves[ind1]=false;
            type[ind1]=node->type;
            if(alpha==int_MIN || alpha==int_MAX)
            {
                DONE_1[ind1]=true;
            }
            else
            {
                DONE_1[ind1]=false;
            }
            return alpha;
 
        }
 
        if(depth>=2 || dist_moves>=8)
        {
            struct_for_sorting aa[dist_moves];
            for(int ix=strt;ix<dist_moves;ix++)
            {
                aa[ix].move.first=moves[ix].first;
                aa[ix].move.second=moves[ix].second;
                aa[ix].parent.first=parent[ix].first;
                aa[ix].parent.second=parent[ix].second;
                aa[ix].move_type=types[ix];
                aa[ix].history= my_HISTORY_saver[moves[ix].first][moves[ix].second][parent[ix].first][parent[ix].second];
                int added=0;
                set<PR>::iterator si;
                for(si=NEIGHBOUR[moves[ix].first][moves[ix].second].begin();si!=NEIGHBOUR[moves[ix].first][moves[ix].second].end();si++)
                {
                    if(node->bd.arr[(*si).first][(*si).second].c==OPP_COLOR)
                    {
                        added++;
                    }            
                }
                if(types[ix]==0)
                {
                    aa[ix].heuristic_val=added+1;
                }
                else
                {
                    aa[ix].heuristic_val=added;
                }
            }
            sort(aa+strt,aa+dist_moves,struct_compare);
            for(int ix=strt;ix<dist_moves;ix++)
            {
                moves[ix].first=aa[ix].move.first;
                moves[ix].second=aa[ix].move.second;
                parent[ix].first=aa[ix].parent.first;
                parent[ix].second=aa[ix].parent.second;
                types[ix]=aa[ix].move_type;
            }
            
            // int curr_val=aa[0].heuristic_val;
            // int st=0,end=dist_moves-1;
            // int ix=0;
            // while(ix<dist_moves)
            // {
            //     st=ix;
            //     curr_val=aa[ix].heuristic_val;
            //     while(aa[ix].heuristic_val==curr_val && ix<dist_moves)ix++;
            //     if(st<ix+1)
            //         sort(aa+st,aa+ix,history_compare);
            // }
            //sort(aa+strt,aa+dist_moves,history_compare);
            
 
            // if(dist_moves>100 && DEPTH-depth>=3 )
            // {
            //    int ix;
            //    for(ix=100;ix<dist_moves;ix++)
            //    {
            //         if(aa[ix].heuristic_val>0)continue;
            //         else break;
            //    }
            //    breaker=ix;
            // }
            // else if(dist_moves>120 && DEPTH-depth>=2 )
            // {
            //    int ix;
            //    for(ix=120;ix<dist_moves;ix++)
            //    {
            //         if(aa[ix].heuristic_val>0)continue;
            //         else break;
            //    }
            //    breaker=ix;
            // }
        }
        
        clock_t curr3 = clock();
        double d3 = (double)(curr3-start)/(double)CLOCKS_PER_SEC;
        if(d3>0.94)
        {
            cout<<parent_x<<" "<<parent_y<<endl;
            cout<<ans_x<<" "<<ans_y<<endl;
            cout<<DEPTH-1<<endl;
            cout<<hash_found<<" "<<total_nodes<<endl;
            ratio=(double)hash_found/total_nodes;
            cout<<ratio<<endl;
            cout<<ans_value<<endl;
            cout<<kya_yaar<<endl;
            cout<<OPENING<<" "<<MIDGAME<<" "<<ENDGAME<<endl;
            cout<<print_input_hashval<<endl;
            exit(0);
        }
        //if(dist_moves>80 && !ENDGAME)dist_moves=80;
        for(int ix = 0 ; ix< dist_moves; ix++)
        {   
            i = moves[ix].first;
            j = moves[ix].second;
            int k = parent[ix].first;
            int l = parent[ix].second;
            int move_type=types[ix];
            //bool iskiller= ( (flag && ix<=selected && ix>0) || (!flag && ix<selected) )?true:false;
            Treenode tr = Treenode(node, k, l, i, j, PLAYER_COLOR,move_type);
           
            int temp;
            temp = alphabeta( &tr, depth-1, alpha, beta);
            if(temp>max || (temp==max && (!ORDER_decider)))
            {   
                max=temp;
                required_type=move_type;
                index=ix;
                if(max>alpha)
                {   alpha=max;
                    if(depth==DEPTH)
                    {
                        temp_x = i;
                        temp_y = j;
                        temp_parent_x=k;
                        temp_parent_y=l;       
 
                    }
                }
                if(beta<=alpha)
                    {
                        //do updation of table
                        if(available[ind1]==false || (available[ind1] && subtree_depth[ind1]<=depth) )
                        {
                            available[ind1]=true;
                            minmax_value[ind1]=alpha;
                            subtree_depth[ind1]=depth;
     
                            bestmove_parent[ind1].first=parent[ix].first;
                            bestmove_parent[ind1].second=parent[ix].second;
                            bestmove[ind1].first=moves[ix].first;
                            bestmove[ind1].second=moves[ix].second;
                            bestmove_type[ind1]=move_type;
                            id1[ind1]=node->hashval;
                            type[ind1]=node->type;
                            zeromoves[ind1]=false;
                            if(alpha==int_MIN || alpha==int_MAX)
                            {
                                DONE_1[ind1]=true;
                            }
                            else
                            {
                                DONE_1[ind1]=false;
                            }
                        }
 
                        // if(move_type==0)
                        // {
                        //     set<PR>::iterator si;
                        //     for(si=NEIGHBOUR[i][j].begin();si!=NEIGHBOUR[i][j].end();si++)
                        //     {
                        //         int ax,ay;
                        //         ax=(*si).first;
                        //         ay=(*si).second;
                        //         if(node->bd.arr[ax][ay].c==PLAYER_COLOR)
                        //         {
                        //             my_HISTORY_saver[i][j][ax][ay] += (1<<depth) ;
                        //         }
                        //     }
                        // }
                        // else
                        // {
                        //     my_HISTORY_saver[i][j][k][l] += (1<<depth) ;
                        // }
 
                        return alpha;
                    }
            }
 
 
        }   
        //do updation of table
        int ix=index;
        //do updation of table
        available[ind1]=true;
        minmax_value[ind1]=alpha;
        subtree_depth[ind1]=depth;
 
        bestmove_parent[ind1].first=parent[ix].first;
        bestmove_parent[ind1].second=parent[ix].second;
        bestmove[ind1].first=moves[ix].first;
        bestmove[ind1].second=moves[ix].second;
        bestmove_type[ind1]=required_type;
        id1[ind1]=node->hashval;
        zeromoves[ind1]=false;
        type[ind1]=node->type;
        if(alpha==int_MIN || alpha==int_MAX)
        {
            DONE_1[ind1]=true;
        }
        else
        {
            DONE_1[ind1]=false;
        }
        return alpha;
 
    }
 
    else
    {   
        int min = 99999999;
        PR parent[max_size+1];
        PR moves[max_size+1];
        int types[max_size+1];
        int spread_count=0;
        if(flag)
        {
            parent[0].first = firstmove_parent.first;
            parent[0].second = firstmove_parent.second;
            moves[0].first=firstmove.first;
            moves[0].second=firstmove.second;
            types[0]=firstmove_type;
            spread_count++;
        }
        spread_count = node->bd.distinct_spread(parent,moves,OPP_COLOR,spread_count);
        for(int tempp=flag?1:0;tempp<spread_count;tempp++)
        {
            types[tempp]=0;
        }
        // int dist_moves=node->bd.distinct_jump(parent,moves,spread_count,OPP_COLOR);
        // if(dist_moves<=2)
        // {
        //     dist_moves=node->bd.distinct_jump2(parent,moves,spread_count,OPP_COLOR);
        //     if(dist_moves>=10)dist_moves=10;
        // }
        // else if(node->bd.red_count+node->bd.blue_count>=35)
        // {
        //     dist_moves=node->bd.distinct_jump2(parent,moves,spread_count,OPP_COLOR);   
        // }
        // if(node->bd.red_count+node->bd.blue_count>=39)
        // {
        //     dist_moves=node->bd.distinct_jump3(parent,moves,spread_count,OPP_COLOR);   
        // }
        // if(dist_moves==0)
        // {
        //     dist_moves=node->bd.distinct_jump3(parent,moves,spread_count,OPP_COLOR);   
        //     if(dist_moves>=5)dist_moves=5;
        // }
        // if(dist_moves==0)
        // {
        //     dist_moves=node->bd.distinct_jump2(parent,moves,dist_moves,OPP_COLOR);
        // }
        // if(node->bd.blue_count+node->bd.red_count>=40)
        // {
        //     dist_moves=node->bd.distinct_jump3(parent,moves,spread_count,OPP_COLOR);
        // }
        // if(dist_moves==0 || node->bd.red_count+node->bd.blue_count>=36)
        // {
        //     dist_moves=node->bd.distinct_jump3(parent,moves,spread_count,PLAYER_COLOR);   
        // }
        
 
        int dist_moves;
        if(OPENING)
        {
            dist_moves=node->bd.distinct_jump3(parent,moves,spread_count,OPP_COLOR);
            
        }
        else if(MIDGAME)
        {
            dist_moves=node->bd.distinct_jump3(parent,moves,spread_count,OPP_COLOR);
        }
        else
        {
            if(node->bd.red_count+node->bd.blue_count<=38)
            {
               dist_moves=node->bd.distinct_jump5(parent,moves,spread_count,OPP_COLOR);   
            }
            else
            dist_moves=node->bd.distinct_jump(parent,moves,spread_count,OPP_COLOR);  
        }
        int tot_pieces=node->bd.blue_count+node->bd.red_count;
        // if( (node->heuristic<=-8 && spread_count>=3 && tot_pieces<=36) || (node->heuristic<=-10 && spread_count>=1 && tot_pieces<=37) )
        // {
        //     return int_MIN;            
        // }
        if(dist_moves==0)
        {
            int ans;
            if(node->heuristic<0)ans=int_MIN;
            else if(node->heuristic>0)ans=int_MAX;
            else ans=0;
            available[ind1]=true;
            minmax_value[ind1]=ans;
            subtree_depth[ind1]=depth;
            zeromoves[ind1]=true;
            id1[ind1]=node->hashval;
            type[ind1]=node->type;
            return ans;
        }
        // if(dist_moves==0 &&  (MIDGAME && tot_pieces<=34) )
        // {
        //     int ans;
        //     if(node->heuristic<0)ans=int_MIN;
        //     else if(node->heuristic>0)ans=int_MAX;
        //     else ans=0;
        //     available[ind1]=true;
        //     minmax_value[ind1]=ans;
        //     subtree_depth[ind1]=depth;
        //     zeromoves[ind1]=true;
        //     id1[ind1]=node->hashval;
        //     type[ind1]=node->type;
        //     return ans;
        // }
        // else if(dist_moves==0 &&  (MIDGAME && tot_pieces>34) )
        //   dist_moves=node->bd.distinct_jump(parent,moves,spread_count,OPP_COLOR);   
 
        if(dist_moves>50)kya_yaar=true;
        
        for(int tempp=spread_count;tempp<dist_moves;tempp++)
        {
            types[tempp]=1;
        }
        int index=0;
        int required_type=0;
        int c_killer=0;
        int strt = flag?1:0;
        int move_no = DEPTH-depth;
        
        int breaker=dist_moves;
        clock_t curr2 = clock();
        double d2 = (double)(curr2-start)/(double)CLOCKS_PER_SEC;
        if(d2>0.93)
        {
            cout<<parent_x<<" "<<parent_y<<endl;
            cout<<ans_x<<" "<<ans_y<<endl;
            cout<<DEPTH-1<<endl;
            cout<<hash_found<<" "<<total_nodes<<endl;
            ratio=(double)hash_found/total_nodes;
            cout<<ratio<<endl;
            cout<<ans_value<<endl;
            cout<<kya_yaar<<endl;
            cout<<OPENING<<" "<<MIDGAME<<" "<<ENDGAME<<endl;
            cout<<print_input_hashval<<endl;
            exit(0);
        }
 
        if(depth==1)
        {
            for(int ix = 0 ; ix< dist_moves; ix++)
            {   
                i = moves[ix].first;
                j = moves[ix].second;
                int k = parent[ix].first;
                int l = parent[ix].second;
                int move_type=types[ix];
                int opp_pieces = (PLAYER_COLOR==RED)?node->bd.red_count:node->bd.blue_count;
                int my_pieces = (OPP_COLOR==RED)?node->bd.red_count:node->bd.blue_count;
                //int added=0;
                set<PR>::iterator si;
                for(si=NEIGHBOUR[moves[ix].first][moves[ix].second].begin();si!=NEIGHBOUR[moves[ix].first][moves[ix].second].end();si++)
                {
                    if(node->bd.arr[(*si).first][(*si).second].c==PLAYER_COLOR)
                    {
                        opp_pieces--;
                        my_pieces++;
                    }            
                }
                if(types[ix]==0)my_pieces++;
                int temp = opp_pieces- my_pieces;
                if(opp_pieces==0){ temp=int_MIN; }         
                if(temp<min || (temp==min && (!ORDER_decider)))
                {
                    min=temp;
                    required_type=move_type;
                    index=ix;
                    if(beta>min)beta=min;
                    if(beta<=alpha)
                        {
                            //do updation of table
                            if(available[ind1]==false || (available[ind1] && subtree_depth[ind1]<=depth) )
                            {
                                available[ind1]=true;
                                minmax_value[ind1]=beta;
                                subtree_depth[ind1]=depth;
                                type[ind1]=node->type;
                                bestmove_parent[ind1].first=parent[ix].first;
                                bestmove_parent[ind1].second=parent[ix].second;
                                bestmove[ind1].first=moves[ix].first;
                                bestmove[ind1].second=moves[ix].second;
                                bestmove_type[ind1]=move_type;
                                id1[ind1]=node->hashval;
                                zeromoves[ind1]=false;
                                if(beta==int_MIN || beta==int_MAX)
                                {
                                    DONE_1[ind1]=true;
                                }
                                else
                                {
                                    DONE_1[ind1]=false;
                                }
                            }
                            // if(move_type==0)
                            // {
                            //     set<PR>::iterator si;
                            //     for(si=NEIGHBOUR[i][j].begin();si!=NEIGHBOUR[i][j].end();si++)
                            //     {
                            //         int ax,ay;
                            //         ax=(*si).first;
                            //         ay=(*si).second;
                            //         if(node->bd.arr[ax][ay].c==OPP_COLOR)
                            //         {
                            //             opp_HISTORY_saver[i][j][ax][ay] += (1<<depth) ;
                            //         }
                            //     }
                            // }
                            // else
                            // {
                            //     opp_HISTORY_saver[i][j][k][l] += (1<<depth) ;
                            // }
                            return beta;
                        }
                }
     
                    
            }
            int ix=index;
            //do updation of table
            available[ind1]=true;
            minmax_value[ind1]=beta;
            subtree_depth[ind1]=depth;
            zeromoves[ind1]=false;
            bestmove_parent[ind1].first=parent[ix].first;
            bestmove_parent[ind1].second=parent[ix].second;
            bestmove[ind1].first=moves[ix].first;
            bestmove[ind1].second=moves[ix].second;
            bestmove_type[ind1]=required_type;
            id1[ind1]=node->hashval;
            type[ind1]=node->type;
            if(beta==int_MIN || beta==int_MAX)
            {
                DONE_1[ind1]=true;
            }
            else
            {
                DONE_1[ind1]=false;
            }
            return beta;
        }
 
        if(depth>=2 || dist_moves>=8)
        {
            struct_for_sorting aa[dist_moves];
            for(int ix=strt;ix<dist_moves;ix++)
            {
                aa[ix].move.first=moves[ix].first;
                aa[ix].move.second=moves[ix].second;
                aa[ix].parent.first=parent[ix].first;
                aa[ix].parent.second=parent[ix].second;
                aa[ix].move_type=types[ix];
                aa[ix].history= opp_HISTORY_saver[moves[ix].first][moves[ix].second][parent[ix].first][parent[ix].second];
                int added=0;
                set<PR>::iterator si;
                for(si=NEIGHBOUR[moves[ix].first][moves[ix].second].begin();si!=NEIGHBOUR[moves[ix].first][moves[ix].second].end();si++)
                {
                    if(node->bd.arr[(*si).first][(*si).second].c==PLAYER_COLOR)
                    {
                        added++;
                    }            
                }
                if(types[ix]==0)
                {
                    aa[ix].heuristic_val=added+1;
                }
                else
                {
                    aa[ix].heuristic_val=added;
                }
            }
            sort(aa+strt,aa+dist_moves,struct_compare);
            for(int ix=strt;ix<dist_moves;ix++)
            {
                moves[ix].first=aa[ix].move.first;
                moves[ix].second=aa[ix].move.second;
                parent[ix].first=aa[ix].parent.first;
                parent[ix].second=aa[ix].parent.second;
                types[ix]=aa[ix].move_type;
            }
 
            // int curr_val=aa[0].heuristic_val;
            // int st=0,end=dist_moves-1;
            // int ix=0;
            // while(ix<dist_moves)
            // {
            //     st=ix;
            //     curr_val=aa[ix].heuristic_val;
            //     while(aa[ix].heuristic_val==curr_val && ix<dist_moves)ix++;
            //     if(st<ix+1)
            //         sort(aa+st,aa+ix,history_compare);
            // }
            clock_t curr3 = clock();
            double d3 = (double)(curr3-start)/(double)CLOCKS_PER_SEC;
            if(d3>0.94)
            {
                cout<<parent_x<<" "<<parent_y<<endl;
                cout<<ans_x<<" "<<ans_y<<endl;
                cout<<DEPTH-1<<endl;
                cout<<hash_found<<" "<<total_nodes<<endl;
                ratio=(double)hash_found/total_nodes;
                cout<<ratio<<endl;
                cout<<ans_value<<endl;
                cout<<kya_yaar<<endl;
                cout<<OPENING<<" "<<MIDGAME<<" "<<ENDGAME<<endl;
                cout<<print_input_hashval<<endl;
                exit(0);
            }
            //sort(aa+strt,aa+dist_moves,history_compare);
            // if(dist_moves>80 && DEPTH-depth>=2 )
            // {
            //    int ix;
            //    for(ix=80;ix<dist_moves;ix++)
            //    {
            //         if(aa[ix].heuristic_val>0)continue;
            //         else break;
            //    }
            //    breaker=ix;
            // }
            // else if(dist_moves>120 && DEPTH-depth>=2 )
            // {
            //    int ix;
            //    for(ix=120;ix<dist_moves;ix++)
            //    {
            //         if(aa[ix].heuristic_val>0)continue;
            //         else break;
            //    }
            //    breaker=ix;
            // }
 
        }
 
        
        //if(dist_moves>50 && !ENDGAME)dist_moves=50;
        for(int ix = 0 ; ix< dist_moves; ix++)
        {   
            i = moves[ix].first;
            j = moves[ix].second;
            int k = parent[ix].first;
            int l = parent[ix].second;
            int move_type=types[ix];
            Treenode tr = Treenode(node, k, l, i, j, OPP_COLOR,move_type);
            int temp;
            temp = alphabeta( &tr, depth-1, alpha, beta);          
            if(temp<min || (temp==min && (!ORDER_decider)))
            {
                min=temp;
                required_type=move_type;
                index=ix;
                if(beta>min)beta=min;
                if(beta<=alpha)
                    {
                        //do updation of table
                        if(available[ind1]==false || (available[ind1] && subtree_depth[ind1]<=depth) )
                        {
                            available[ind1]=true;
                            minmax_value[ind1]=beta;
                            subtree_depth[ind1]=depth;
                            type[ind1]=node->type;
                            bestmove_parent[ind1].first=parent[ix].first;
                            bestmove_parent[ind1].second=parent[ix].second;
                            bestmove[ind1].first=moves[ix].first;
                            bestmove[ind1].second=moves[ix].second;
                            bestmove_type[ind1]=move_type;
                            id1[ind1]=node->hashval;
                            zeromoves[ind1]=false;
                            if(beta==int_MIN || beta==int_MAX)
                            {
                                DONE_1[ind1]=true;
                            }
                            else
                            {
                                DONE_1[ind1]=false;
                            }
                        }
                        // if(move_type==0)
                        // {
                        //     set<PR>::iterator si;
                        //     for(si=NEIGHBOUR[i][j].begin();si!=NEIGHBOUR[i][j].end();si++)
                        //     {
                        //         int ax,ay;
                        //         ax=(*si).first;
                        //         ay=(*si).second;
                        //         if(node->bd.arr[ax][ay].c==OPP_COLOR)
                        //         {
                        //             opp_HISTORY_saver[i][j][ax][ay] += (1<<depth) ;
                        //         }
                        //     }
                        // }
                        // else
                        // {
                        //     opp_HISTORY_saver[i][j][k][l] += (1<<depth) ;
                        // }
                        return beta;
                    }
            }
 
                
        }
        int ix=index;
        //do updation of table
        available[ind1]=true;
        minmax_value[ind1]=beta;
        subtree_depth[ind1]=depth;
        zeromoves[ind1]=false;
        bestmove_parent[ind1].first=parent[ix].first;
        bestmove_parent[ind1].second=parent[ix].second;
        bestmove[ind1].first=moves[ix].first;
        bestmove[ind1].second=moves[ix].second;
        bestmove_type[ind1]=required_type;
        id1[ind1]=node->hashval;
        type[ind1]=node->type;
        if(beta==int_MIN || beta==int_MAX)
        {
            DONE_1[ind1]=true;
        }
        else
        {
            DONE_1[ind1]=false;
        }
        return beta;
    }
    
 
}
 
void alphabeta_control(Treenode *head)
{   
    
    DEPTH=1;
    while(1)
    {
        clock_t curr = clock();
        double d = (double)(curr-start)/(double)CLOCKS_PER_SEC;
        if(d>0.925)
        {
            break;
        }
        int alpha = -100000000;
        int beta = 100000000;
        int xx = alphabeta(head, DEPTH, alpha, beta);
        ans_value=xx;
        ans_x=temp_x;ans_y=temp_y;
        parent_x=temp_parent_x;
        parent_y=temp_parent_y;
        if(DEPTH>=MAX_DEPTH)break;
        DEPTH += INCRE;
    }
 
}
 
 
 
int main()
{   
    start=clock();
    srand(13);
    // for(int i=0;i<6;i++)
    // {
    //     for(int j=0;j<7;j++)
    //     {
    //         my_HISTORY_saver[i][j]=0;
    //         opp_HISTORY_saver[i][j]=0;
    //     }
    // }
    //for(int i=0;i<25;i++)cuttoff_defined[i][0]=cuttoff_defined[i][1]=false;
    for(int i=0;i<M;i++)
    {
        available[i]=false;
        id1[i]=-1;
        DONE_1[i]=false;
        zeromoves[i]=false;
    }
    for(int i=0;i<6;i++)
    {
        for(int j=0;j<7;j++)
        {
            for(int k=0;k<3;k++)
            {
                ulll hashval =0;
                for(int it=0;it<64;it++)
                {
                    hashval += ( (rand()%2)*(1<<it) );
                }
                HASH_VALUE_PER_PIECE[i][j][k]=hashval;
            }
        }
    }
    turn_HASHVAL=0;
    for(int it=0;it<64;it++)
    {
        turn_HASHVAL += ( (rand()%2)*(1<<it) );
    }                
 
    for(int i=0;i<6;i++)
    {
        for(int j=0;j<7;j++)
        {
            NEIGHBOUR[i][j].clear();
            DIST2NEIGHBOUR[i][j].clear();
        }
    }
    for(int i=0;i<6;i++)
    {
        for(int j=0;j<7;j++)
        {
            if(i-1>=0)
            {
                NEIGHBOUR[i][j].insert(PR(i-1,j));
            }
            if(i+1<=5)
            {
                NEIGHBOUR[i][j].insert(PR(i+1,j));
            }
            
            if(j-1>=0)
            {
                NEIGHBOUR[i][j].insert(PR(i,j-1));
            }
            if(j+1<=6)
            {
                NEIGHBOUR[i][j].insert(PR(i,j+1));
            }
 
            if(j%2==0)
            {
                if(i-1>=0)
                {
                    if(j-1>=0)
                    {
                        NEIGHBOUR[i][j].insert(PR(i-1,j-1));
                    }
                    if(j+1<=6)
                    {
                        NEIGHBOUR[i][j].insert(PR(i-1,j+1));
                    }
                }
            }
            else
            {
                if(i+1<=5)
                {
                    if(j-1>=0)
                    {
                        NEIGHBOUR[i][j].insert(PR(i+1,j-1));
                    }
                    if(j+1<=6)
                    {
                        NEIGHBOUR[i][j].insert(PR(i+1,j+1));
                    }
                }
            }
 
        }
    }
 
    for(int i=0;i<6;i++)
    {
        for(int j=0;j<7;j++)
        {
            set<PR>::iterator sni;
            for(sni=NEIGHBOUR[i][j].begin();sni!=NEIGHBOUR[i][j].end();sni++)
            {
                int k = (*sni).first;
                int l = (*sni).second;
                set<PR>::iterator sni2;
                for(sni2=NEIGHBOUR[k][l].begin();sni2!=NEIGHBOUR[k][l].end();sni2++)
                {
                    int p = (*sni2).first;
                    int q = (*sni2).second;
                    if(NEIGHBOUR[i][j].find(PR(p,q))==NEIGHBOUR[i][j].end() && !(p==i && q==j) )
                    {
                        if(DIST2NEIGHBOUR[i][j].find(PR(p,q))==DIST2NEIGHBOUR[i][j].end())
                            DIST2NEIGHBOUR[i][j].insert(PR(p,q));
                    }
                }
            }
        }
    }
    // int total_pieces=0;
    Board obj = Board();
    for(int i=0;i<6;i++)
    {   
        for(int j=0;j<7;j++)
        {
            int temp;
            cin>>temp;
            if(temp==0)continue;
            Color clr = temp==1?RED:BLUE;
            obj.arr[i][j].c=clr;
            if(temp==1)obj.red_count++;
            else obj.blue_count++;
        }
    }
    // if(DIST2NEIGHBOUR[0][4].find(PR(2,5))!=DIST2NEIGHBOUR[0][4].end())
    // {
    //     cout<<"mkve";
    // }
    int moves_till_now;
    cin>>moves_till_now;
    Treenode head = Treenode(&obj, moves_till_now);
    MAX_DEPTH=100;
    INCRE=1;
 
    ans_x=-1;
    ans_y=-1;
 
    int temp;
    cin>>temp;
    if(temp==1)PLAYER_COLOR=RED;
    else PLAYER_COLOR=BLUE;
    OPP_COLOR = (PLAYER_COLOR==RED)?BLUE:RED;
    OPENING=MIDGAME=ENDGAME=false;
    int total_pieces = obj.red_count+obj.blue_count;
    if(total_pieces<=21)OPENING=true;
    else if(total_pieces<=33)MIDGAME=true;
    else ENDGAME=true;
    ORDER_decider = (rand()%2==0)?false:true;
    if(ORDER_decider==false)
    {
      ORDER_decider = (rand()%2==0)?false:true;
    }
    if(ORDER_decider==false)
    {
      ORDER_decider = (rand()%2==0)?false:true;
    }
    ORDER_decider=true;
    if(moves_till_now>=88)
    {
        ENDGAME=true;
        OPENING=false;
        MIDGAME=false;
    }
 
    alphabeta_control(&head);
    if(ans_x==-1 ||  (ans_x==0 && ans_y==0 && parent_x==0 && parent_y==0) )
    {
        for(int i=0;i<6;i++)
        {
            for(int j=0;j<7;j++)
            {
                set<PR>::iterator si;
                for(si=DIST2NEIGHBOUR[i][j].begin();si!=DIST2NEIGHBOUR[i][j].end();si++)
                {
                    int k = (*si).first;
                    int l = (*si).second;
                    if(obj.arr[i][j].c==NONE && obj.arr[k][l].c==PLAYER_COLOR)
                    {
                        cout<<i<<" "<<j<<endl;
                        cout<<k<<" "<<l<<endl;
                        cout<<" problem related to no moves";
                        return 0;
                    }
                }
            }
        }
    }
    cout<<parent_x<<" "<<parent_y<<endl;
    cout<<ans_x<<" "<<ans_y<<endl;
    cout<<DEPTH-1<<endl;
    cout<<hash_found<<" "<<total_nodes<<endl;
    ratio=(double)hash_found/total_nodes;
    cout<<ratio<<endl;
    cout<<ans_value<<endl;
    cout<<kya_yaar<<endl;
    cout<<OPENING<<" "<<MIDGAME<<" "<<ENDGAME<<endl;
    cout<<print_input_hashval<<endl;
    return 0;
 
}
