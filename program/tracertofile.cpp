// -*- mode: C++; c-file-style: "stroustrup"; c-basic-offset: 4; indent-tabs-mode: nil; -*-

/* tracer - Utility for printing UPPAAL XTR trace files.
   Copyright (C) 2006 Uppsala University and Aalborg University.
   Copyright (C) 2017 Aalborg University.

   This library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public License
   as published by the Free Software Foundation; either version 2.1 of
   the License, or (at your option) any later version.

   This library is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with this library; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
   USA
*/

#include <cassert>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <limits>
#include <map>
#include <stdexcept>
#include <string>
#include <vector>
#include <list>
#include <iterator>
#include <sstream>

#include "system.h"
#include "xmlwriter.h"

#include <deque>
#include <vector>
#include <map>
#include <exception>
#include <algorithm>
#include <chrono>




/* This utility takes an UPPAAL model in the UPPAAL intermediate
 * format and a UPPAAL XTR trace file and prints trace to stdout in a
 * human readable format.
 *
 * The utility basically contains two parsers: One for the
 * intermediate format and one for the XTR format. You may want to use
 * them a starting point for writing analysis tools.
 *
 * Notice that the intermediate format uses a global numbering of
 * clocks, variables, locations, etc. This is in contrast to the XTR
 * format, which makes a clear distinction between e.g. clocks and
 * variables and uses process local number of locations and
 * edges. Care must be taken to convert between these two numbering
 * schemes.
 */

using std::ofstream;
using std::ostream;
using std::istream;
using std::ifstream;
using std::cout;
using std::cerr;
using std::endl;
using std::string;
using std::vector;
using std::map;
using std::to_string;
using std::stringstream;

struct milestoneValue
{
    string name;
    int value;
};

struct taskValue
{
    string name;
    string agent;
    int value;
};

struct parsed_state_agent
{
    int Id;
    milestoneValue Milestone;
    string Task;
    vector<string> FinishedTasks;
    int Iteration;  
};

struct parsed_action_agent
{
    int Id;
    string Type;
    string Target;
    vector<int> TimeInt;
};

struct parsed_action
{
    vector<parsed_action_agent> Agents;
};

struct parsed_state
{
    vector<parsed_state_agent> Agents;
};

struct parsed_result
{
    int Result;
    vector<parsed_state> States;
    vector<parsed_action> Actions;
};

struct agent_locations
{
    int id;
    string name;
    vector<string> locations;
};

struct agent_task_no
{
    int id;
    int no;
};


//Struct to improve the output of the parser.
struct glob
{
    //These are the list of names that parser will look for when assigning a move type to each agent.
    vector<string> moveStartFrom;
    vector<string> moveStartTo;
    vector<string> moveFinishFrom;
    vector<string> moveFinishTo;

    //This is the name of the that the parser will set the move type to.
    string moveStart;
    string moveFinish;

    //These are the list of names that parser will look for when assigning a task type to each agent.
    vector<string> taskStartTo;
    vector<string> taskStartFrom;
    vector<string> taskFinishTo;
    vector<string> taskFinishFrom;

    //This is the name of the that the parser will set the task type to.
    string taskStart;
    string taskFinish;


    //To enable the parser to know if a system is a move or a task each need to begin with something to identify them by. "t_" for task is an example
    string milestoneNameIdentifier;
    string taskNameIdentifier;

    //Names of the milestones
    vector<milestoneValue> milestoneValues;

    //The id of the agent and then the number of task it needs to complete before starting over
    vector<agent_task_no> agentsTaskNo;

    //Time is not really used since the parser can't get the current time. So the time itervall will always be 0 - maxTime
    int maxTime;

    //The int value that shows that a task is completed.
    int taskCompleteVar;

    //The number of tasks.
    int maxTaskNo;

    //If there are some moves that are for setting up or something like that. Then thin can be used to ignore them. 0 will start from the beginning.
    int startOffset;

    //Number of agents in the system
    int noOfAgents;
};

/* Representation of a memory cell.
 */
struct cell_t
{
    enum type_t: int { CONST, CLOCK, VAR, META, SYS_META, COST, LOCATION, FIXED };
    enum flags_t: int { NONE, COMMITTED, URGENT };
    /** The type of the cell. */
    type_t type;

    /** Name of cell. Not all types have names. */
    string name;

    union
    {
        int value;
        struct
        {
            int nr;
        } clock;
        struct
        {
            int min;
            int max;
            int init;
            int nr;
        } var;
        struct
        {
            int min;
            int max;
            int init;
            int nr;
        } meta;
        struct
        {
            int min;
            int max;
        } sys_meta;
        struct
        {
            flags_t flags;
            int process;
            int invariant;
        } location;
        struct
        {
            int min;
            int max;
        } fixed;
    };
};

/* Representation of a process.
 */
struct process_t
{
    int initial;
    string name;
    vector<int> locations;
    vector<int> edges;
};

/* Representation of an edge.
 */
struct edge_t
{
    int process;
    int source;
    int target;
    int guard;
    int sync;
    int update;
};

/* The UPPAAL model in intermediate format.
 */
static vector<cell_t> layout;
static vector<int> instructions;
static vector<process_t> processes;
static vector<edge_t> edges;
static map<int,string> expressions;

/* For convenience we keep the size of the system here.
 */
static size_t processCount = 0;
static size_t variableCount = 0;
static size_t clockCount = 0;
int unParsedTransiNameLoc = 0;

milestoneValue STONE0 = 
{
    "STONE0",
    0
};

milestoneValue STONE1 = 
{
    "STONE1",
    1
};

milestoneValue PRIMARYCRUSHER0 = 
{
    "PRIMARYCRUSHER0",
    2
};

milestoneValue SECONDARYCRUSHER0 = 
{
    "SECONDARYCRUSHER0",
    3
};

milestoneValue ONTHEWAY = 
{
    "ONTHEWAY",
    -1
};

glob globs = 
{
    //moveStartFrom
    {"P1"},
    //moveStartTo
    {"F1T2"},
    //moveFinishFrom
    {"F1T2"},
    //moveFinishTo
    {"P2"},

    //moveStart
    "Move Start",
    //moveFinish
    "Move Finish",

    //taskStartTo
    {"Executing"},
    //taskStartFrom
    {"Waiting", "Idle"},
    //taskFinishTo
    {"Idle"},
    //taskFinishFrom
    {"Executing"},

    //taskStart
    "Task Start",
    //taskFinish
    "Task Finish",

    //milestoneNameIdentifier
    "m_",
    //taskNameIdentifier
    "t_",

    //milestoneValues
    {STONE0, STONE1, PRIMARYCRUSHER0, SECONDARYCRUSHER0, ONTHEWAY},

    //Each of agents no of tasks
    {{0, 2} ,{1, 2}, {2, 3}},

    //maxTime
    3600,
    //taskCompleteVar
    2,
    //taskNo
    3,
    //startOffset
    1,
    //noOfAgents
    3
};
vector<parsed_state> states;
vector<parsed_action> actions;
parsed_result results;
vector<agent_locations> AgentsLocations;

vector<vector<string>> unParsedStates;
vector<vector<vector<string>>> unParsedTransition;

/* These are mappings from variable and clock indicies to
 * the names of these variables and clocks.
 */
static vector<string> clocks;
static vector<string> variables;

//CODE FROM https://github.com/UPPAALModelChecker/utap tracer.cpp starts here and ends on line 965 not including some parts of main
//It does however take what the old parser would print out to the console and adds it to a list of outputs. unParsedTransitions and unParsedStates 

/* Thrown by parser upon parse errors.
 */
class invalid_format : public std::runtime_error
{
public:
    explicit invalid_format(const string&  arg) : runtime_error(arg) {}
};

/* Reads one line from file. Skips comments.
 */
bool read(istream& file, string& str)
{
    do
    {
        if (!getline(file, str))
        {
            return false;
        }
    } while (!str.empty() && str[0] == '#');
    return true;
}

/* Reads one line and asserts that it contains a (terminating) dot
 */
istream& readdot(istream& is)
{
    string str;
    getline(is, str);
    if (str.empty())
    {
        getline(is, str);
    }
    if (str != ".")
    {
        cerr << "Expecting a line with '.' but got '" << str << "'" << endl;
        assert(false);
        exit(EXIT_FAILURE);
    }
    return is;
}

inline
istream& skipspaces(istream& is)
{
    while (is.peek() == ' ')
    {
        is.get();
    }
    return is;
}

/* Parser for intermediate format.
 */
void loadIF(istream& file)
{
    string str;
    string section;
    char name[32];
    int index;

    while (getline(file, section))
    {
        if (section == "layout")
        {
            cell_t cell;
            while (read(file, str) && !str.empty() && !isspace(str[0]))
            {
                char s[5];
                auto cstr = str.c_str();

                if (sscanf(cstr, "%d:clock:%d:%31s", &index,
                           &cell.clock.nr, name) == 3)
                {
                    cell.type = cell_t::CLOCK;
                    cell.name = name;
                    clocks.emplace_back(name);
                    clockCount++;
                }
                else if (sscanf(cstr, "%d:const:%d", &index,
                                &cell.value) == 2)
                {
                    cell.type = cell_t::CONST;
                }
                else if (sscanf(cstr, "%d:var:%d:%d:%d:%d:%31s", &index,
                                &cell.var.min, &cell.var.max, &cell.var.init,
                                &cell.var.nr, name) == 6)
                {
                    cell.type = cell_t::VAR;
                    cell.name = name;
                    variables.emplace_back(name);
                    variableCount++;
                }
                else if (sscanf(cstr, "%d:meta:%d:%d:%d:%d:%31s", &index,
                                &cell.meta.min, &cell.meta.max, &cell.meta.init,
                                &cell.meta.nr, name) == 6)
                {
                    cell.type = cell_t::META;
                    cell.name = name;
                    variables.emplace_back(name);
                    variableCount++;
                }
                else if (sscanf(cstr, "%d:sys_meta:%d:%d:%31s", &index,
                                &cell.sys_meta.min, &cell.sys_meta.max, name) == 4)
                {
                    cell.type = cell_t::SYS_META;
                    cell.name = name;
                }
                else if (sscanf(cstr, "%d:location::%31s", &index, name) == 2)
                {
                    cell.type = cell_t::LOCATION;
                    cell.location.flags = cell_t::NONE;
                    cell.name = name;
                }
                else if (sscanf(cstr, "%d:location:committed:%31s", &index, name) == 2)
                {
                    cell.type = cell_t::LOCATION;
                    cell.location.flags = cell_t::COMMITTED;
                    cell.name = name;
                }
                else if (sscanf(cstr, "%d:location:urgent:%31s", &index, name) == 2)
                {
                    cell.type = cell_t::LOCATION;
                    cell.location.flags = cell_t::URGENT;
                    cell.name = name;
                }
                else if (sscanf(cstr, "%d:static:%d:%d:%31s", &index,
                                &cell.fixed.min, &cell.fixed.max,
                                name) == 4)
                {
                    cell.type = cell_t::FIXED;
                    cell.name = name;
                }
                else if (sscanf(cstr, "%d:%5s", &index, s) == 2
                         && strcmp(s, "cost") == 0)
                {
                    cell.type = cell_t::COST;
                }
                else
                {
                    throw invalid_format(str);
                }

                layout.push_back(cell);
            }
#if defined(ENABLE_CORA) || defined(ENABLE_PRICED)
            cell.type = cell_t::VAR;
            cell.var.min = std::numeric_limits<int32_t>::min();
            cell.var.max = std::numeric_limits<int32_t>::max();
            cell.var.init = 0;

            cell.name = "infimum_cost";
            cell.var.nr = variableCount++;
            variables.push_back(cell.name);
            layout.push_back(cell);

            cell.name = "offset_cost";
            cell.var.nr = variableCount++;
            variables.push_back(cell.name);
            layout.push_back(cell);

            for (size_t i=1; i<clocks.size(); ++i) {
                cell.name = "#rate[";
                cell.name.append(clocks[i]);
                cell.name.append("]");
                cell.var.nr = variableCount++;
                variables.push_back(cell.name);
                layout.push_back(cell);
            }
#endif
        }
        else if (section == "instructions")
        {
            while (read(file, str) && !str.empty() && (!isspace(str[0]) || str[0]=='\t'))
            {
                int address;
                int values[4];
                if (str[0]=='\t')
                {   // skip pretty-printed instruction text
                    continue;
                }
                int cnt = sscanf(str.c_str(), "%d:%d%d%d%d", &address,
                                 &values[0], &values[1], &values[2], &values[3]);
                if (cnt < 2)
                {
                    throw invalid_format("In instruction section");
                }

                for (int i = 0; i < cnt-1; ++i)
                {
                    instructions.push_back(values[i]);
                }
            }
        }
        else if (section == "processes")
        {
            while (read(file, str) && !str.empty() && !isspace(str[0]))
            {
                process_t process;
                if (sscanf(str.c_str(), "%d:%d:%31s",
                           &index, &process.initial, name) != 3)
                {
                    throw invalid_format("In process section");
                }
                process.name = name;
                processes.push_back(process);
                processCount++;
            }
        }
        else if (section == "locations")
        {
            while (read(file, str) && !str.empty() && !isspace(str[0]))
            {
                int index;
                int process;
                int invariant;

                if (sscanf(str.c_str(), "%d:%d:%d", &index, &process, &invariant) != 3)
                {
                    throw invalid_format("In location section");
                }

                layout[index].location.process = process;
                layout[index].location.invariant = invariant;
                processes[process].locations.push_back(index);
            }
        }
        else if (section == "edges")
        {
            while (read(file, str) && !str.empty() && !isspace(str[0]))
            {
                edge_t edge;

                if (sscanf(str.c_str(), "%d:%d:%d:%d:%d:%d", &edge.process,
                           &edge.source, &edge.target,
                           &edge.guard, &edge.sync, &edge.update) != 6)
                {
                    throw invalid_format("In edge section");
                }

                processes[edge.process].edges.push_back(edges.size());
                edges.push_back(edge);
            }
        }
        else if (section == "expressions")
        {
            while (read(file, str) && !str.empty() && !isspace(str[0]))
            {
                if (sscanf(str.c_str(), "%d", &index) != 1)
                {
                    throw invalid_format("In expression section");
                }

                /* Find expression string (after the third colon). */
                auto *s = str.c_str();
                int cnt = 3;
                while (cnt && *s)
                {
                    cnt -= (*s == ':');
                    s++;
                }
                if (cnt)
                {
                    throw invalid_format("In expression section");
                }

                /* Trim white space. */
                while (*s && isspace(*s))
                {
                    s++;
                }
                auto *t = s + strlen(s) - 1;
                while (t >= s && isspace(*t))
                {
                    t--;
                }

                expressions[index] = string(s, t+1);
            }
        }
        else
        {
            throw invalid_format("Unknown section");
        }
    }
};

/* A bound for a clock constraint. A bound consists of a value and a
 * bit indicating whether the bound is strict or not.
 */
struct bound_t
{
    int value   : 31; // The value of the bound
    bool strict : 1;  // True if the bound is strict
};

/* The bound (infinity, <).
 */
static bound_t infinity = { std::numeric_limits<int32_t>::max() >> 1, true };

/* The bound (0, <=).
 */
static bound_t zero = { 0, false };

/* A symbolic state. A symbolic state consists of a location vector, a
 * variable vector and a zone describing the possible values of the
 * clocks in a symbolic manner.
 */
class State
{
public:
    State();
    explicit State(istream& file);
    State(const State& s) = delete;
    State(State&& s) = delete;
    ~State();

    int &getLocation(int i)              { return locations[i]; }
    int &getVariable(int i)              { return integers[i]; }
    bound_t &getConstraint(int i, int j) { return dbm[i * clockCount + j]; }

    int getLocation(int i) const              { return locations[i]; }
    int getVariable(int i) const              { return integers[i]; }
    bound_t getConstraint(int i, int j) const { return dbm[i * clockCount + j]; }
private:
    vector<int> locations;
    vector<int> integers;
    bound_t *dbm;
    void allocate();
};

State::~State()
{
    delete[] dbm;
}

State::State()
{
    /* Allocate. */
    locations.resize(processCount);
    integers.resize(variableCount);
    dbm = new bound_t[clockCount * clockCount];

    /* Fill with default values. */
    std::fill(dbm, dbm + clockCount * clockCount, infinity);

    /* Set diagonal and lower bounds to zero. */
    for (size_t i = 0; i < clockCount; i++)
    {
        getConstraint(0, i) = zero;
        getConstraint(i, i) = zero;
    }
}

State::State(istream& file): State()
{
    /* Read locations.  */
    for (auto& l: locations)
    {
        file >> l;
    }
    file >> readdot;

    /* Read DBM. */
    int i, j, bnd;
    while (file >> i >> j >> bnd)
    {
        file >> readdot;
        getConstraint(i, j).value = bnd >> 1;
        getConstraint(i, j).strict = bnd & 1;
    }
    file.clear();
    file >> readdot;

    /* Read integers. */
    for (auto& v: integers)
    {
        file >> v;
    }
    file >> readdot;
}

struct Edge
{
    int process;
    int edge;
    vector<int> select;
};

/* A transition consists of one or more edges. Edges are indexes from
 * 0 in the order they appear in the input file.
 */
struct Transition
{
    vector<Edge> edges;
    explicit Transition(istream& file);
};

//Here the unParsedTransitions are filled.
Transition::Transition(istream& file)
{
    int process, edge, select;
    while (file >> process >> edge)
    {
        Edge e{process, edge};
        file >> skipspaces;
        while (file.peek()!='\n' && file.peek()!=';')
        {
            if (file >> select)
            {
                e.select.push_back(select);
            }
            else
            {
                cerr << "Transition format error" << endl;
                exit(EXIT_FAILURE);
            }
            file >> skipspaces;
        }
        if (file.get()=='\n') // old format without ';'
        {   // old format indexes edges from 1, hence convert to 0-base
            e.edge--;
        }
        edges.push_back(e);
    }
    file.clear();
    file >> readdot;
}

/* Output operator for a symbolic state. Prints the location vector,
 * the variables and the zone of the symbolic state.
 */
//Here the unParsedStates are filled.
ostream &operator << (ostream &o, const State &state)
{
    vector<string> outState;
    stringstream outputState;
    /* Print location vector. */
    for (size_t p = 0; p < processCount; p++)
    {
        int idx = processes[p].locations[state.getLocation(p)];
        outputState << processes[p].name << '.' << layout[idx].name << " ";

        string temp;
        outputState >> temp;
        outState.push_back(temp);
        outputState << endl;
    }

    /* Print variables. */
    for (size_t v = 0; v < variableCount; v++)
    {
        outputState << variables[v] << "=" << state.getVariable(v) << ' ';

        string temp;
        outputState >> temp;
        outState.push_back(temp);
        outputState << endl;
    }
    int i = 5;
    i++;
    /* Print clocks. */
    for (size_t i = 0; i < clockCount; i++)
    {
        for (size_t j = 0; j < clockCount; j++)
        {
            if (i != j)
            {
                bound_t bnd = state.getConstraint(i, j);

                if (bnd.value != infinity.value)
                {
                    string temp1;
                    string temp2;
                    string temp3;
                    string temp4;
                    stringstream temp5;

                    temp5 << clocks[i] << endl;
                    temp5 >> temp1;
                    temp5 << clocks[j] << endl;;
                    temp5 >> temp2;
                    temp5 << (bnd.strict ? "<" : "<=") << endl;;
                    temp5 >> temp3;
                    temp5 << bnd.value << endl;;
                    temp5 >> temp4;

                    outputState << clocks[i] << "-" << clocks[j]
                         << (bnd.strict ? "<" : "<=") << bnd.value << " ";

                    string temp;
                    outputState >> temp;
                    outState.push_back(temp);
                    outputState << endl;
                }
            }
        }
    }
    unParsedStates.push_back(outState);

    return o;
}

/* Output operator for a transition. Prints all edges in the
 * transition including the source, destination, guard,
 * synchronisation and assignment.
 */
ostream &operator << (ostream &o, const Transition &t)
{
    vector<vector<string>> outTrans;
    for (auto& edge: t.edges)
    {
        int eid = processes[edge.process].edges[edge.edge];
        int src = edges[eid].source;
        int dst = edges[eid].target;
        int guard = edges[eid].guard;
        int sync = edges[eid].sync;
        int update = edges[eid].update;

        string temp;
        vector<string> outTransition;

        outTransition.push_back(processes[edge.process].name);
 
        outTransition.push_back(".");
        outTransition.push_back(layout[src].name);
        outTransition.push_back(" -> ");
        outTransition.push_back(processes[edge.process].name);
        outTransition.push_back(".");
        outTransition.push_back(layout[dst].name);
        
        if (!edge.select.empty()) {
            auto s=edge.select.begin(), se=edge.select.end();


            outTransition.push_back(" [");

            temp = *s;
            outTransition.push_back(temp);

            while (++s != se)
            {   
                outTransition.push_back(",");
                temp = *s;
                outTransition.push_back(temp);
            } 

            outTransition.push_back(temp = "]");
        }

        outTransition.push_back(" {");
        outTransition.push_back(expressions[guard]);
        outTransition.push_back("; ");
        outTransition.push_back(expressions[sync]);
        outTransition.push_back("; ");
        outTransition.push_back(expressions[update]);
        outTransition.push_back(";} ");
        outTrans.push_back(outTransition);
    }
    unParsedTransition.push_back(outTrans);
    return o;
}

/* Read and print a trace file.
 */
void loadTrace(istream& file)
{
    cout << State(file);

    for (;;)
    {
        /* Skip white space. */
        file >> skipspaces;

        /* A dot terminates the trace. */
        if (file.peek() == '.')
        {
            file.get();
            break;
        }

        /* Read a state and a transition. */
        State state(file);
        Transition transition(file);

        /* Print transition and state. */
        cout << transition;
        cout << state;

    }
}
///////////////////////////////////////////// code from tracer.cpp ends here


//Fills the agen locations
//This is so the id of agents and their locations can be matched together.
void fillAgentsLocations()
{
    if(processes.empty())
        return;
    else
    {
        vector<string> agNames;
        vector<string> procNames;
        vector<int> startIndexOfNewName;
        string prev = "";

        //I is one since i dont know any good way to ignore the Rong processes.
        for(int i = globs.startOffset; i < processes.size(); i++)
        {
            process_t temp = processes.at(i);
            string procName = temp.name;

            int index = procName.find_last_of("_")+1;
            string agName = procName.substr(index, procName.size()-index);
            if(i != 1)
            {
                int added = 0;
                for(int j = 0; j < agNames.size(); j++)
                {
                    if(agNames.at(j) == agName)
                    {
                        added = 1;
                        break;
                    }
                }
                if(added == 0)
                {
                    agNames.push_back(agName);
                }   
            }
            else
            {
                agNames.push_back(agName);
                startIndexOfNewName.push_back(i);
            }

            string name = procName.substr(0, index-1);
            procNames.push_back(name);
        }

        for(int i = 0; i < globs.noOfAgents; i++)
        {
            agent_locations agentLoc;

            agentLoc.id = i;
            agentLoc.name = agNames.at(i);
            vector<string> locations;

            for(int j = 0; j < procNames.size(); j++)
            {
                for(int l = 0; l < processes.size(); l++)
                {
                    if(processes.at(l).name.find(agNames.at(i)) != string::npos && processes.at(l).name.find(procNames.at(j)) != string::npos)
                    {
                        locations.push_back(procNames.at(j));
                    }
                }
            }

            agentLoc.locations = locations;
            AgentsLocations.push_back(agentLoc);
        }
    }
 
}

//Parses the tracer to something that easily can be printet to an xml file.
void parseResults()
{
    if(unParsedStates.empty() || unParsedTransition.empty())
    {
        results.Result = 0;
    }
    else
    {
        results.Result = 1;

        for(int i = 1; i < unParsedStates.size(); i++)
        {

            //Filles the actions
            parsed_action action;
            for(int j = 0; j < globs.noOfAgents; j++)
            {
                parsed_action_agent actionAgent;

                if(!(i >= unParsedTransition.size()))
                {
                    int index = unParsedTransiNameLoc;
                    int transiLocFrom = 0;
                    int transiLocTo = 4;

                    string transiFrom = unParsedTransition.at(i).at(index).at(transiLocFrom);
                    if(transiFrom.find(AgentsLocations.at(j).name) != string::npos)
                    {
                        actionAgent.Id = j;

                        //Need to fixer lower bound time;
                        actionAgent.TimeInt.push_back(0);
                        actionAgent.TimeInt.push_back(globs.maxTime);

                        //Checks if the action move is in a task or a milestone
                        //Task
                        if(transiFrom.find(globs.taskNameIdentifier) != string::npos)
                        {
                            for(int f = 0; f < globs.taskStartFrom.size(); f++)
                            {
                                for(int t = 0; t < globs.taskStartTo.size(); t++)
                                {
                                    //Checks the combinations of values that means that a task is starting
                                    if(unParsedTransition.at(i).at(index).at(transiLocFrom+2).find(globs.taskStartFrom.at(f)) != string::npos 
                                    && unParsedTransition.at(i).at(index).at(transiLocTo+2).find(globs.taskStartTo.at(t)) != string::npos)
                                    {
                                        actionAgent.Type = globs.taskStart;
                                        actionAgent.Target = transiFrom + "." + unParsedTransition.at(i).at(index).at(transiLocTo+2);                 
                                    }
                                }
                            }    

                            for(int f = 0; f < globs.taskFinishFrom.size(); f++)
                            {
                                for(int t = 0; t < globs.taskFinishTo.size(); t++)
                                {
                                    //Checks the combinations of values that means that a task is done
                                    if(unParsedTransition.at(i).at(index).at(transiLocFrom+2).find(globs.taskFinishFrom.at(f)) != string::npos 
                                    && unParsedTransition.at(i).at(index).at(transiLocTo+2).find(globs.taskFinishTo.at(t)) != string::npos)
                                    {
                                        actionAgent.Type = globs.taskFinish;
                                        actionAgent.Target = transiFrom + "." + unParsedTransition.at(i).at(index).at(transiLocTo+2);
                                    }
                                }
                            }    
                        }

                        //Milestones
                        else if(transiFrom.find(globs.milestoneNameIdentifier) != string::npos)
                        {
                            for(int f = 0; f < globs.moveStartFrom.size(); f++)
                            {
                                for(int t = 0; t < globs.moveStartTo.size(); t++)
                                {
                                    //Checks the combinations of values that means that a move is starting
                                    if(unParsedTransition.at(i).at(index).at(transiLocFrom+2).find(globs.moveStartFrom.at(f)) != string::npos 
                                    && unParsedTransition.at(i).at(index).at(transiLocTo+2).find(globs.moveStartTo.at(t)) != string::npos)
                                    {
                                        actionAgent.Type = globs.moveStart ;
                                        actionAgent.Target = transiFrom + "." + unParsedTransition.at(i).at(index).at(transiLocTo+2);
                                    }
                                }
                            }

                            for(int f = 0; f < globs.moveFinishFrom.size(); f++)
                            {
                                for(int t = 0; t < globs.moveFinishTo.size(); t++)
                                { 
                                    //Checks the combinations of values that means that a move is done
                                    if(unParsedTransition.at(i).at(index).at(transiLocFrom+2).find(globs.moveFinishFrom.at(f)) != string::npos 
                                    && unParsedTransition.at(i).at(index).at(transiLocTo+2).find(globs.moveFinishTo.at(t)) != string::npos)
                                    {
                                        actionAgent.Type = globs.moveFinish;
                                        actionAgent.Target = transiFrom + "." + unParsedTransition.at(i).at(index).at(transiLocTo+2);
                                    }
                                }
                            } 
                                   
                        }
                        action.Agents.push_back(actionAgent);
                    }     
                }   
            }
            results.Actions.push_back(action);

            //Filles the parsed states.
            parsed_state state;
            for(int j = 0; j < globs.noOfAgents; j++)
            {
                parsed_state_agent stateAgent;

                for(int k = 0; k < unParsedStates.at(i).size(); k++)
                {
                    //Should be changed to something that can be added into globs.
                    
                    string find = "agents[" + to_string(j) + "]" + ".a_position";
                    string variable = unParsedStates.at(i).at(k);
                    //Gets the int value from the unParsedStates and matches it with the milestoneValue
                    if(variable.find(find) != string::npos)
                    {
                        string value = variable.substr(variable.find("=")+1, variable.size()-variable.find("=")-1);
                        for(int l = 0; l < globs.milestoneValues.size(); l++)
                        {
                            if(globs.milestoneValues.at(l).value == stoi(value))
                            {
                                stateAgent.Milestone = globs.milestoneValues.at(l);
                            }
                        }
                    }
                }

                if(i == 1)
                {
                    stateAgent.Id = j;
                    stateAgent.Iteration = 0;
                    state.Agents.push_back(stateAgent);
                }

                else
                {   
                    parsed_action prevAction = results.Actions.back();
                    stateAgent = results.States.back().Agents.at(j);
                    vector<string> compTask = stateAgent.FinishedTasks;


                    for(int k = 0; k < prevAction.Agents.size(); k++)
                    {
                        if(j == prevAction.Agents.at(k).Id)
                        {
                            if(prevAction.Agents.at(k).Type == globs.taskStart)
                            {
                                stateAgent.Task = prevAction.Agents.at(k).Target;              
                            }

                            else if(prevAction.Agents.at(k).Type == globs.taskFinish)
                            {
                                string task = results.States.back().Agents.at(j).Task;
                                int added = 0;
                                //Makes sure that there is only one ex of each task in the compTask list
                                for(int l = 0; l < compTask.size(); l++)
                                {
                                    if(compTask.at(l) == task)
                                    {
                                        added = 1;
                                        break;
                                    }
                                }    

                                if(added == 0)
                                {
                                    compTask.push_back(task);
                                }
                            }
                        }
                    }

                    //If the size of the comptask is the size of the task for the agent then the iteration will increase on and the list of comptask will be removed.
                    if(stateAgent.FinishedTasks.size() == globs.agentsTaskNo.at(j).no)
                    {
                        stateAgent.Iteration++;
                        stateAgent.FinishedTasks.clear();
                    }
                    else
                        stateAgent.FinishedTasks = compTask;               

                    state.Agents.push_back(stateAgent);
                    
                }    
            }  
            results.States.push_back(state);
        }
    }
}


//Prints the parsed result into the inputfile and also provides the time for parsing
//Warning. This just tries to print out all the data under specific tags and does not check if its a good xml file.
void printParsedResultsToXMLFile(parsed_result Result, string file_name, auto duration)
{
    ofstream file(file_name);
    xmlw::XmlStream xml(file);

    xml << xmlw::prolog()
    << xmlw::tag("Traces") << xmlw::attr("result") << results.Result << xmlw::chardata() << xmlw::chardata() << "Time: " << xmlw::chardata() << duration.count() << xmlw::chardata() << "ms" << xmlw::chardata() << "\n";
    
    for(int i = 0; i < results.States.size(); i++)
    {
        xml << xmlw::chardata() << "    " << xmlw::tag("State") << xmlw::chardata() << "\n"; 
        
        //First prints out the stage
        for(int j = 0; j < results.States.at(i).Agents.size(); j++)
        {
            xml << xmlw::chardata() << "        "
            << xmlw::tag("Agent") << xmlw::attr("id") << j << xmlw::chardata() << "\n"
            << xmlw::chardata() << "            "
            << xmlw::tag("Milestone") << xmlw::chardata() << results.States.at(i).Agents.at(j).Milestone.name << xmlw::endtag() << xmlw::chardata() << "\n"
            << xmlw::chardata() << "            "
            << xmlw::tag("Task") << xmlw::chardata() << results.States.at(i).Agents.at(j).Task << xmlw::endtag() << xmlw::chardata() << "\n"
            << xmlw::chardata() << "            "
            << xmlw::tag("Finish") << xmlw::chardata() << "\n";

            //Prints if there are any completed tasks
            for(int k = 0; k < results.States.at(i).Agents.at(j).FinishedTasks.size(); k++)
            {
                xml << xmlw::chardata() << "                "
                << xmlw::tag("Task")
                << xmlw::chardata() << results.States.at(i).Agents.at(j).FinishedTasks.at(k)
                << xmlw::endtag() << xmlw::chardata() << "\n";
            }

            xml << xmlw::chardata() << "            " << xmlw::endtag() << xmlw::chardata() << "\n"
            << xmlw::chardata() << "            "
            << xmlw::tag("Iteration") << xmlw::chardata() << results.States.at(i).Agents.at(j).Iteration << xmlw::endtag() << xmlw::chardata() << "\n"
            << xmlw::chardata() << "        " << xmlw::endtag() <<  xmlw::chardata() <<"\n";
        }
        xml << xmlw::chardata() << "    " << xmlw::endtag() << xmlw::chardata() << "\n";

        //Prints out the action after that, as long as is not the final stage.
        if(i < results.States.size()-1)
        {
            xml << xmlw::chardata() << "    " << xmlw::tag("Action") << xmlw::chardata() << "\n";
            
            for(int j = 0; j < results.Actions.at(i).Agents.size(); j++)
            {
                xml << xmlw::chardata() << "        "
                << xmlw::tag("Agent") << xmlw::attr("id") << j << xmlw::chardata() << "\n"
                << xmlw::chardata() << "            "
                << xmlw::tag("Type") << xmlw::chardata() << results.Actions.at(i).Agents.at(j).Type << xmlw::endtag() << xmlw::chardata() << "\n"
                << xmlw::chardata() << "            "
                << xmlw::tag("Target") << xmlw::chardata() << results.Actions.at(i).Agents.at(j).Target << xmlw::endtag()<< xmlw::chardata() << "\n"
                << xmlw::chardata() << "            " 
                << xmlw::tag("Time") << xmlw::chardata() << results.Actions.at(i).Agents.at(j).TimeInt.at(0) << "-" <<  results.Actions.at(i).Agents.at(j).TimeInt.at(1) 
                << xmlw::endtag()<< xmlw::chardata() << "\n"
                << xmlw::chardata() << "        " 
                << xmlw::endtag() << xmlw::chardata() << "\n";
            }
            xml << xmlw::chardata() << "    " << xmlw::endtag() << xmlw::chardata() << "\n";
        }
    }
    xml << xmlw::endtag();  
}

int main(int argc, char *argv[])
{
    try
    {
        //Makes sure that all the arguments are set.
        if (argc < 3)
        {
            printf("Synopsis: %s <if> <trace>\n", argv[0]);
            exit(1);
        }

        /* Load model in intermediate format.
         */
        if (strcmp(argv[1], "-") == 0)
        {
            loadIF(std::cin);
        }
        else
        {
            ifstream file(argv[1]);
            if (!file)
            {
                perror(argv[1]);
                exit(EXIT_FAILURE);
            }
            loadIF(file);
            file.close();
        }

        /* Load trace.
         */
        ifstream file(argv[2]);
        if (!file)
        {
            perror(argv[2]);
            exit(EXIT_FAILURE);
        }
        loadTrace(file);
        file.close();
    }
    catch (std::exception &e)

    {
        cerr << "Cought exception: " << e.what() << endl;
    }

    string file_name;
    file_name = argv[3];

    fillAgentsLocations();

    //Start the timer.
    auto start = std::chrono::high_resolution_clock::now();
    parseResults();
    auto stop = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(stop-start);

    //prints the result to xml.
    printParsedResultsToXMLFile(results, file_name, duration);

}