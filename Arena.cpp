#include <iostream>
#include <iomanip>
#include <sstream>
#include <fstream>
#include <unistd.h>
#include <sys/wait.h>
#include <sys/ioctl.h>
#include <poll.h>
#include <array>
#include <random>
#include <chrono>
#include <omp.h>
#include <limits>
#include <algorithm>
#include <map>
#include <thread>
#include <csignal>
using namespace std;
using namespace std::chrono;

constexpr bool Debug_AI{false},Timeout{false};
constexpr int PIPE_READ{0},PIPE_WRITE{1};
constexpr int N{2};//Number of players, 1v1
constexpr double FirstTurnTime{1*(Timeout?1:10)},TimeLimit{0.05*(Timeout?1:10)};
constexpr int W{23},H{21};

bool stop{false};//Global flag to stop all arena threads when SIGTERM is received

struct vec3{
    int x,y,z;
};

struct vec{
    int x,y;
    inline void operator+=(const vec &a)noexcept{
        x+=a.x;
        y+=a.y;
    }
    inline vec operator*(const int a)const noexcept{
        return vec{x*a,y*a};
    }
    inline vec operator+(const vec &a)const noexcept{
        return vec{x+a.x,y+a.y};
    }
    inline vec operator-(const vec &a)const noexcept{
        return vec{x-a.x,y-a.y};
    }
    inline bool operator==(const vec &a)const noexcept{
        return x==a.x && y==a.y;
    }
    inline bool valid()const noexcept{
        return x<W && y<H && x>=0 && y>=0;
    }
    inline vec3 toCube()const noexcept{
        const int x3{x-(y-(y&1))/2};
        return vec3{x3,-(x3+y),y};
    }
};

struct vecf{
    double x,y;
    inline double norm2()const noexcept{
        return pow(x,2)+pow(y,2);
    }
    inline double norm()const noexcept{
        return sqrt(norm2());
    }
    inline void normalise()noexcept{
        const double n{1.0/norm()};
        x*=n;
        y*=n;
    }
    inline double operator*(const vec &a)const noexcept{
        return x*a.x+y*a.y;
    }
};

constexpr array<vec,6> Move_Vec_Array_Even{vec{1,0},vec{0,-1},vec{-1,-1},vec{-1,0},vec{-1,1},vec{0,1}};
constexpr array<vec,6> Move_Vec_Array_Odd{vec{1,0},vec{1,-1},vec{0,-1},vec{-1,0},vec{0,1},vec{1,1}};
constexpr array<array<vec,6>,2> Move_Vec_Array{Move_Vec_Array_Even,Move_Vec_Array_Odd};

inline vec Move_Vec(const vec &r,const int angle)noexcept{
    const bool odd{r.y%2!=0};
    return Move_Vec_Array[odd][angle];
}

inline int Opposite_Angle(const int angle)noexcept{
    return (angle+3)%6;
}

inline int Dist(const vec &a,const vec &b)noexcept{
    vec3 a2=a.toCube(),b2=b.toCube();
    return max({abs(a2.x-b2.x),abs(a2.y-b2.y),abs(a2.z-b2.z)});
}

inline vec Neighbour(const vec &r,const int angle)noexcept{
    return r+Move_Vec(r,angle);
}

struct ship{
    int id;
    vec r;
    int angle,speed,rum,owner,cd,mine_cd;
    inline vec front()const noexcept{
        return r+Move_Vec(r,angle);
    }
    inline vec back()const noexcept{
        return r+Move_Vec(r,Opposite_Angle(angle));
    }
    inline void Blow(const vec &hit)noexcept{
        if(hit==r){
            rum=max(0,rum-50);
        }
        else if(hit==front() || hit==back()){
            rum=max(0,rum-25);
        }
    }
    inline bool IsBoat(const vec &a)const noexcept{
        return a==r || a==back() || a==front();
    }
    inline void Splash(const vec &source)noexcept{
        if(Dist(back(),source)<=1 || Dist(r,source)<=1 || Dist(front(),source)<=1){
            rum-=10;
        }
    }
};

struct barrel{
    int id;
    vec r;
    int rum;
};

struct cannonball{
    int id,shooter_id;
    vec target;
    int turns;
};

struct mine{
    int id;
    vec r;
};

struct state{
    int entityId;
    vector<ship> S;
    vector<barrel> B;
    vector<mine> M;
    vector<cannonball> C;
    inline void clear()noexcept{
        B.clear();
        M.clear();
        S.clear();
        C.clear();
    }
    inline void Purge()noexcept{
        C.erase(remove_if(C.begin(),C.end(),[](const cannonball &c){return c.turns<=0;}),C.end());
        S.erase(remove_if(S.begin(),S.end(),[](const ship &s){return s.rum<=0;}),S.end());
    }
    inline void Blow(const vec &hit)noexcept{
        auto barrel_it=find_if(B.begin(),B.end(),[&](const barrel &b){return b.r==hit;});
        auto mine_it=find_if(M.begin(),M.end(),[&](const mine &m){return m.r==hit;});
        if(barrel_it!=B.end()){
            B.erase(barrel_it);
        }
        else if(mine_it!=M.end()){
            M.erase(mine_it);
            for_each(S.begin(),S.end(),[&](ship &s){s.Splash(hit);});
        }
        else{
           for_each(S.begin(),S.end(),[&](ship &s){s.Blow(hit);}); 
        }
    }
    inline bool free(const vec &r)noexcept{
        const bool no_barrel{find_if(B.begin(),B.end(),[&](const barrel &b){return b.r==r;})==B.end()};
        const bool no_mine{find_if(M.begin(),M.end(),[&](const mine &m){return m.r==r;})==M.end()};
        const bool no_ship{find_if(S.begin(),S.end(),[&](const ship &ship){return ship.IsBoat(r);})==S.end()};
        return no_barrel && no_ship && no_mine;
    }
};

const array<string,8> MoveType2Str{"FIRE","MINE","PORT","STARBOARD","FASTER","SLOWER","WAIT","MOVE"};

enum move_type{FIRE=0,MINE=1,PORT=2,STARBOARD=3,FASTER=4,SLOWER=5,WAIT=6,MOVE=7};

struct play{
    move_type type;
    vec target;
};

typedef map<int,play> strat;

inline ostream& operator<<(ostream &os,const vec &r)noexcept{
    os << r.x << " " << r.y;
    return os;
}

inline istream& operator>>(istream &is,vec &r)noexcept{
    is >> r.x >> r.y;
    return is;
}

inline ostream& operator<<(ostream &os,const play &mv)noexcept{
    os << MoveType2Str[mv.type];
    if(mv.type==FIRE){
        os << " " << mv.target;
    }
    return os;
}

inline string EmptyPipe(const int fd){
    int nbytes;
    if(ioctl(fd,FIONREAD,&nbytes)<0){
        throw(4);
    }
    string out;
    out.resize(nbytes);
    if(read(fd,&out[0],nbytes)<0){
        throw(4);
    }
    return out;
}

struct AI{
    int id,pid,outPipe,errPipe,inPipe;
    string name;
    inline void stop(){
        if(alive()){
            kill(pid,SIGTERM);
            int status;
            waitpid(pid,&status,0);//It is necessary to read the exit code for the process to stop
            if(!WIFEXITED(status)){//If not exited normally try to "kill -9" the process
                kill(pid,SIGKILL);
            }
        }
    }
    inline bool alive()const{
        return kill(pid,0)!=-1;//Check if process is still running
    }
    inline void Feed_Inputs(const string &inputs){
        if(write(inPipe,&inputs[0],inputs.size())!=inputs.size()){
            throw(5);
        }
    }
    inline ~AI(){
        close(errPipe);
        close(outPipe);
        close(inPipe);
        stop();
    }
};

void StartProcess(AI &Bot){
    int StdinPipe[2];
    int StdoutPipe[2];
    int StderrPipe[2];
    if(pipe(StdinPipe)<0){
        perror("allocating pipe for child input redirect");
    }
    if(pipe(StdoutPipe)<0){
        close(StdinPipe[PIPE_READ]);
        close(StdinPipe[PIPE_WRITE]);
        perror("allocating pipe for child output redirect");
    }
    if(pipe(StderrPipe)<0){
        close(StderrPipe[PIPE_READ]);
        close(StderrPipe[PIPE_WRITE]);
        perror("allocating pipe for child stderr redirect failed");
    }
    int nchild{fork()};
    if(nchild==0){//Child process
        if(dup2(StdinPipe[PIPE_READ],STDIN_FILENO)==-1){// redirect stdin
            perror("redirecting stdin");
            return;
        }
        if(dup2(StdoutPipe[PIPE_WRITE],STDOUT_FILENO)==-1){// redirect stdout
            perror("redirecting stdout");
            return;
        }
        if(dup2(StderrPipe[PIPE_WRITE],STDERR_FILENO)==-1){// redirect stderr
            perror("redirecting stderr");
            return;
        }
        close(StdinPipe[PIPE_READ]);
        close(StdinPipe[PIPE_WRITE]);
        close(StdoutPipe[PIPE_READ]);
        close(StdoutPipe[PIPE_WRITE]);
        close(StderrPipe[PIPE_READ]);
        close(StderrPipe[PIPE_WRITE]);
        execl(Bot.name.c_str(),Bot.name.c_str(),(char*)NULL);//(char*)Null is really important
        //If you get past the previous line its an error
        perror("exec of the child process");
    }
    else if(nchild>0){//Parent process
        close(StdinPipe[PIPE_READ]);//Parent does not read from stdin of child
        close(StdoutPipe[PIPE_WRITE]);//Parent does not write to stdout of child
        close(StderrPipe[PIPE_WRITE]);//Parent does not write to stderr of child
        Bot.inPipe=StdinPipe[PIPE_WRITE];
        Bot.outPipe=StdoutPipe[PIPE_READ];
        Bot.errPipe=StderrPipe[PIPE_READ];
        Bot.pid=nchild;
    }
    else{//failed to create child
        close(StdinPipe[PIPE_READ]);
        close(StdinPipe[PIPE_WRITE]);
        close(StdoutPipe[PIPE_READ]);
        close(StdoutPipe[PIPE_WRITE]);
        perror("Failed to create child process");
    }
}

inline bool IsValidMove(const state &S,const AI &Bot,const string &M){
    const int ships{static_cast<int>(count_if(S.S.begin(),S.S.end(),[&](const ship &s){return s.owner==Bot.id;}))};
    return count(M.begin(),M.end(),'\n')==ships;//as many lines as ships
}

string GetMove(const state &S,AI &Bot,const int turn){
    pollfd outpoll{Bot.outPipe,POLLIN};
    time_point<system_clock> Start_Time{system_clock::now()};
    string out;
    while(static_cast<duration<double>>(system_clock::now()-Start_Time).count()<(turn==1?FirstTurnTime:TimeLimit) && !IsValidMove(S,Bot,out)){
        double TimeLeft{(turn==1?FirstTurnTime:TimeLimit)-static_cast<duration<double>>(system_clock::now()-Start_Time).count()};
        if(poll(&outpoll,1,TimeLeft)){
            out+=EmptyPipe(Bot.outPipe);
        }
    }
    return out;
}

inline bool Has_Won(const array<AI,N> &Bot,const int idx)noexcept{
    if(!Bot[idx].alive()){
        return false;
    }
    for(int i=0;i<N;++i){
        if(i!=idx && Bot[i].alive()){
            return false;
        }
    }
    return true;
}

inline bool All_Dead(const array<AI,N> &Bot)noexcept{
    for(const AI &b:Bot){
        if(b.alive()){
            return false;
        }
    }
    return true;
}

template <bool verbose> void Simulate(state &S,const array<strat,2> &M){
    map<int,int> RumToDrop;
    for(ship &s:S.S){//Accelerations, decelerations, rum decrease
        --s.rum;
        RumToDrop[s.id]=min(30,s.rum);
        const play &mv=M[s.owner].at(s.id);
        if(mv.type==SLOWER){
            s.speed=max(0,s.speed-1);
        }
        else if(mv.type==FASTER){
            s.speed=min(2,s.speed+1);
        }
        else if(mv.type==FIRE && s.cd==0 && Dist(s.front(),mv.target)<=10){
            S.C.push_back(cannonball{S.entityId++,s.id,mv.target,2+static_cast<int>(round(Dist(s.front(),mv.target)/3.0))});//2 because i move cannonballs after
            s.cd=2;
        }
        else if(mv.type==MINE && s.mine_cd==0){
            vec mine_spot=Neighbour(s.back(),Opposite_Angle(s.angle));
            if(mine_spot.valid() && S.free(mine_spot)){
                S.M.push_back(mine{S.entityId++,mine_spot});
                s.mine_cd=5;
            }
        }
        s.cd=max(0,s.cd-1);
        s.mine_cd=max(0,s.mine_cd-1);
    }
    //Movement and collisions
    for(int spd=1;spd<=2;++spd){
        vector<ship> S_Before=S.S;
        for(ship &s:S.S){
            if(s.speed>=spd){
                vec next=Neighbour(s.r,s.angle);
                if(next.valid()){
                    s.r=next;
                }
                else{
                    s.speed=0;
                }
            }
        }
        while(true){
            vector<int> colliding_boats;
            for(int i=0;i<S.S.size();++i){
                const ship &s=S.S[i];
                if(s.speed>=spd){
                    for(int j=0;j<S.S.size();++j){
                        if(i!=j){//Don't check collisions with yourself
                            const ship &s2=S.S[j];
                            const vec new_front=s.front();
                            if(s2.IsBoat(new_front)){//Collision
                                colliding_boats.push_back(i);
                                if(s2.front()==s.front()){
                                    colliding_boats.push_back(j);
                                }
                            }
                        }
                    }
                }
            }
            for(const int a:colliding_boats){
                ship &s=S.S[a];
                s.speed=0;//Stop ship
                s.r=S_Before[a].r;//Put back in original position
            }
            if(colliding_boats.size()==0){
                break;
            }
        }
        for(ship &s:S.S){
            if(s.speed>=spd){
                const vec new_front=s.front();
                auto barrel_it=find_if(S.B.begin(),S.B.end(),[&](const barrel &b){return b.r==new_front;});
                if(barrel_it!=S.B.end()){
                    const barrel &b=*barrel_it;
                    s.rum=min(100,s.rum+b.rum);
                    S.B.erase(barrel_it);
                }
                auto mine_it=find_if(S.M.begin(),S.M.end(),[&](const mine &m){return m.r==new_front;});
                if(mine_it!=S.M.end()){
                    s.rum-=25;
                    for_each(S.S.begin(),S.S.end(),[&](ship &s2){if(s2.id!=s.id)s2.Splash(mine_it->r);});
                    S.M.erase(mine_it);
                }
            }
        }
    }
    //Turns
    vector<ship> S_Before=S.S;
    for(ship &s:S.S){
        const play &mv=M[s.owner].at(s.id);
        if(mv.type==STARBOARD || mv.type==PORT){//Rotation
            if(mv.type==STARBOARD){
                s.angle=s.angle==0?5:s.angle-1;
            }
            else if(mv.type==PORT){
                s.angle=s.angle==5?0:s.angle+1;
            }
        }
    }
    while(true){
        vector<int> colliding_boats;
        for(int i=0;i<S.S.size();++i){
            const ship &s=S.S[i];
            const play &mv=M[s.owner].at(s.id);
            if(mv.type==STARBOARD || mv.type==PORT){//Rotation
                for(int j=0;j<S.S.size();++j){
                    if(j!=i){//Don't check collision with yourself
                        const ship &s2=S.S[j];
                        const vec new_front=s.front(),new_front2=s2.front(),new_back=s.back(),new_back2=s2.back();
                        if(s.IsBoat(new_front2) || s2.IsBoat(new_front) || s.IsBoat(new_back2) || s2.IsBoat(new_back)){//Collision
                            colliding_boats.push_back(i);
                            colliding_boats.push_back(j);
                        } 
                    }
                }
            }
        }
        for(const int a:colliding_boats){
            ship &s=S.S[a];
            s.speed=0;//Stop ship
            s.angle=S_Before[a].angle;
        }
        if(colliding_boats.size()==0){
            break;
        }
    }
    for(ship &s:S.S){
        const play &mv=M[s.owner].at(s.id);
        if(mv.type==STARBOARD || mv.type==PORT){//Rotation
            const vec new_front=s.front(),new_back=s.back();
            auto barrel_it=find_if(S.B.begin(),S.B.end(),[&](const barrel &b){return b.r==new_front || b.r==new_back;});
            if(barrel_it!=S.B.end()){
                const barrel &b=*barrel_it;
                s.rum=min(100,s.rum+b.rum);
                S.B.erase(barrel_it);
            }
            auto mine_it=find_if(S.M.begin(),S.M.end(),[&](const mine &m){return m.r==new_front || m.r==new_back;});
            if(mine_it!=S.M.end()){
                s.rum-=25;
                for_each(S.S.begin(),S.S.end(),[&](ship &s2){if(s2.id!=s.id)s2.Splash(mine_it->r);});
                S.M.erase(mine_it);
            }
        }
    }
    for(cannonball &c:S.C){
        --c.turns;
        if(c.turns==0){
            S.Blow(c.target);
        }
    }
    for(const ship &s:S.S){
        if(s.rum<=0 && RumToDrop[s.id]>0){
            S.B.push_back(barrel{S.entityId++,s.r,RumToDrop[s.id]});
        }
    }
    S.Purge();
}

inline bool Player_Alive(const state &S,const int player)noexcept{
    return find_if(S.S.begin(),S.S.end(),[&](const ship &s){return s.owner==player;})!=S.S.end();
}

inline double Angle(const vec &a,const vec &b)noexcept{//Angle from a to b, taken from referee
    const double dy =(b.y-a.y)*sqrt(3)/2;
    const double dx = b.x-a.x+((a.y-b.y)&1)*0.5;
    double angle=-atan2(dy,dx)*3/M_PI;
    if(angle<0){
        angle+=6;
    }else if(angle>=6){
        angle-=6;
    }
    return angle;
}

play Basic_Move(const state &S,const ship &s,const vec &target){//Translated from CG referee
    if(s.r==target || s.speed==2){
        return {SLOWER};
    }
    else if(s.speed==1){
        vec n=Neighbour(s.r,s.angle);
        if(!n.valid()){//Hitting edge of map
            return {SLOWER};
        }
        if(n==target){// Target reached at next turn
            return {WAIT};
        }

        const double targetAngle{Angle(s.r,target)};
        const double angleStraight{min(abs(s.angle-targetAngle),6-abs(s.angle-targetAngle))};
        const double anglePort{min(abs((s.angle+1)-targetAngle),abs((s.angle-5)-targetAngle))};
        const double angleStarboard{min(abs((s.angle+5)-targetAngle),abs((s.angle-1)-targetAngle))};

        const double centerAngle{Angle(s.r,vec{W/2,H/2})};
        const double anglePortCenter{min(abs((s.angle+1)-centerAngle),abs((s.angle-5)-centerAngle))};
        const double angleStarboardCenter{min(abs((s.angle+5)-centerAngle),abs((s.angle-1)-centerAngle))};
        if(Dist(s.r,target)==1 && angleStraight>1.5){// Next to target with bad angle, slow down then rotate (avoid to turn around the target!)
            return {SLOWER};
        }
        int min_dist{Dist(n,target)};
        play best_move{WAIT};
        //Test port
        vec nextPort=Neighbour(s.r,(s.angle+1)%6);
        if(nextPort.valid()){
            const int dist{Dist(nextPort,target)};
            if(dist<min_dist || (dist==min_dist && anglePort<angleStraight-0.5) ){
                min_dist=dist;
                best_move={PORT};
            }
        }
        // Test starboard
        vec nextStarboard=Neighbour(s.r,(s.angle+5)%6);
        if(nextStarboard.valid()){
            const int dist{Dist(nextStarboard,target)};
            if(dist<min_dist
                    || (dist==min_dist && angleStarboard<anglePort-0.5 && best_move.type==PORT)
                    || (dist==min_dist && angleStarboard<angleStraight-0.5 && best_move.type==WAIT)
                    || (dist==min_dist && best_move.type==PORT && angleStarboard==anglePort
                            && angleStarboardCenter<anglePortCenter)
                    || (dist==min_dist && best_move.type==PORT && angleStarboard==anglePort
                            && angleStarboardCenter==anglePortCenter && (s.angle==1||s.angle==4))){
                min_dist=dist;
                best_move={STARBOARD};
            }
        }
        return best_move;
    }
    else if(s.speed==0){
        const double targetAngle{Angle(s.r,target)};
        const double angleStraight{min(abs(s.angle-targetAngle),6-abs(s.angle-targetAngle))};
        const double anglePort{min(abs((s.angle+1)-targetAngle),abs((s.angle-5)-targetAngle))};
        const double angleStarboard{min(abs((s.angle+5)-targetAngle),abs((s.angle-1)-targetAngle))};

        const double centerAngle{Angle(s.r,vec{W/2,H/2})};
        const double anglePortCenter{min(abs((s.angle+1)-centerAngle),abs((s.angle-5)-centerAngle))};
        const double angleStarboardCenter{min(abs((s.angle+5)-centerAngle),abs((s.angle-1)-centerAngle))};

        vec n=Neighbour(s.r,s.angle);
        play best_move{WAIT};
        if(anglePort<=angleStarboard){
            best_move={PORT};
        }
        if(angleStarboard<anglePort || angleStarboard==anglePort && angleStarboardCenter<anglePortCenter
                || angleStarboard==anglePort && angleStarboardCenter==anglePortCenter && (s.angle==1 || s.angle==4)){
            best_move={STARBOARD};
        }
        if(n.valid() && angleStraight<=anglePort && angleStraight<=angleStarboard){
            best_move={FASTER};
        }
        return best_move;
    }
}

strat StringToStrat(const state &S,const AI &Bot,const string &M_str){
    strat M;
    vector<int> Boat_Id;
    for(const ship &s:S.S){
        if(s.owner==Bot.id){
            Boat_Id.push_back(s.id);
        }
    }
    stringstream ss(M_str);
    for(const int id:Boat_Id){
        string line,type;
        getline(ss,line);
        stringstream ss2(line);
        ss2 >> type;
        if(type=="FIRE"){
            vec target;
            ss2 >> target;
            M[id]=play{FIRE,target};
        }
        else if(type=="MINE"){
            M[id]=play{MINE};
        }
        else if(type=="FASTER"){
            M[id]=play{FASTER};
        }
        else if(type=="SLOWER"){
            M[id]=play{SLOWER};
        }
        else if(type=="PORT"){
            M[id]=play{PORT};
        }
        else if(type=="STARBOARD"){
            M[id]=play{STARBOARD};
        }
        else if(type=="WAIT"){
            M[id]=play{WAIT};
        }
        else if(type=="MOVE"){
            vec target;
            ss2 >> target;
            M[id]=Basic_Move(S,*find_if(S.S.begin(),S.S.end(),[&](const ship &s){return s.id==id;}),target);
        }
        else{
            cerr << "Invalid move from AI " << Bot.name << ": " << M_str << endl;
            throw(2);
        }
    }
    return M;
}

int Play_Game(const array<string,N> &Bot_Names,state &S){
    array<AI,N> Bot;
    for(int i=0;i<N;++i){
        Bot[i].id=i;
        Bot[i].name=Bot_Names[i];
        StartProcess(Bot[i]);
    }
    int turn{0};
    while(++turn>0 && !stop){
        array<strat,2> M;
        for(int i=0;i<N;++i){
            if(Bot[i].alive()){
                stringstream ss;
                const int playerShips{static_cast<int>(count_if(S.S.begin(),S.S.end(),[&](const ship &s){return s.owner==Bot[i].id;}))};
                vector<mine> Visible_Mines;
                for(const mine &m:S.M){
                    bool visible{false};
                    for(const ship &s:S.S){
                        if(s.owner==Bot[i].id && Dist(s.r,m.r)<=5){
                            visible=true;
                            break;
                        }
                    }
                    if(visible){
                        Visible_Mines.push_back(m);
                    }
                }
                ss << playerShips << endl;
                ss << S.S.size()+Visible_Mines.size()+S.C.size()+S.B.size() << endl;
                for(const ship &s:S.S){
                    ss << s.id << " " << "SHIP" << " " << s.r << " " << s.angle << " " << s.speed << " " << s.rum << " " << (s.owner==Bot[i].id?1:0) << endl;
                }
                for(const mine &m:Visible_Mines){
                    ss << m.id << " " << "MINE" << " " << m.r << " " << -1 << " " << -1 << " " << -1 << " " << -1 << endl;
                }
                for(const cannonball &c:S.C){
                    ss << c.id << " " << "CANNONBALL" << " " << c.target << " " << c.shooter_id << " " << c.turns << " " << -1 << " " << -1 << endl;
                }
                for(const barrel &b:S.B){
                    ss << b.id << " " << "BARREL" << " " << b.r << " " << b.rum << " " << -1 << " " << -1 << " " << -1 << endl; 
                }
                try{
                    Bot[i].Feed_Inputs(ss.str());
                    M[i]=StringToStrat(S,Bot[i],GetMove(S,Bot[i],turn));
                    //cerr << M[i] << endl;
                }
                catch(int ex){
                    if(ex==1){//Timeout
                        cerr << "Loss by Timeout of AI " << Bot[i].id << " name: " << Bot[i].name << endl;
                    }
                    else if(ex==5){
                        cerr << "AI " << Bot[i].name << " died before being able to give it inputs" << endl;
                    }
                    Bot[i].stop();
                }
            }
        }
        for(int i=0;i<2;++i){
            string err_str{EmptyPipe(Bot[i].errPipe)};
            if(Debug_AI){
                ofstream err_out("log.txt",ios::app);
                err_out << err_str << endl;
            }
            if(Has_Won(Bot,i)){
                //cerr << i << " has won in " << turn << " turns" << endl;
                return i;
            }
        }
        if(All_Dead(Bot)){
            return -1;
        }
        Simulate<false>(S,M);
        for(int i=0;i<N;++i){
            if(!Player_Alive(S,i)){
                Bot[i].stop();
            }
        }
        for(int i=0;i<2;++i){
            if(Has_Won(Bot,i)){
                //cerr << i << " has won in " << turn << " turns" << endl;
                return i;
            }
        }
        if(turn==200){
            array<int,2> Total_Rum;
            for(int i=0;i<2;++i){
                Total_Rum[i]=accumulate(S.S.begin(),S.S.end(),0,[&](const int a,const ship &s){return a+(s.owner==i?s.rum:0);});
            }
            return Total_Rum[0]>Total_Rum[1]?0:Total_Rum[1]>Total_Rum[0]?1:-1;
        }
    }
    return -2;
}

int Play_Round(array<string,N> Bot_Names){
    default_random_engine generator(system_clock::now().time_since_epoch().count());
    uniform_int_distribution<int> Swap_Distrib(0,1);
    const bool player_swap{Swap_Distrib(generator)==1};
    if(player_swap){
        swap(Bot_Names[0],Bot_Names[1]);
    }

    uniform_int_distribution<int> Ship_Count(1,3),Mine_Count(5,10),Barrel_Count(10,26),Angle_Distrib(0,5);
    state S;
    S.entityId=0;
    const int shipsPerPlayer{Ship_Count(generator)},mines{Mine_Count(generator)},barrels{Barrel_Count(generator)};

    for(int i=0;i<shipsPerPlayer;++i){
        const int xMin{1+i*W/shipsPerPlayer},xMax{(i+1)*W/shipsPerPlayer-2};
        uniform_int_distribution<int> X_Distrib(xMin,xMax),Y_Distrib(1,H/2-2);
        const vec r{X_Distrib(generator),Y_Distrib(generator)};
        const int angle{Angle_Distrib(generator)};
        S.S.push_back({S.entityId++,r,angle,0,100,0,0,0});//id,pos,angle,speed,rum,owner,cd
        S.S.push_back({S.entityId++,vec{r.x,H-1-r.y},(6-angle)%6,0,100,1,0,0});
    }

    while(S.M.size()<mines){
        uniform_int_distribution<int> X_Distrib(1,W-2),Y_Distrib(1,H/2);
        const vec r{X_Distrib(generator),Y_Distrib(generator)};
        if(S.free(r)){
            if(r.y!=H-1-r.y){
                S.M.push_back(mine{S.entityId++,vec{r.x,H-1-r.y}});
            }
            S.M.push_back(mine{S.entityId++,r});
        }
    }

    while(S.B.size()<barrels){
        uniform_int_distribution<int> X_Distrib(1,W-2),Y_Distrib(1,H/2),Rum_Distrib(10,20);
        const vec r{X_Distrib(generator),Y_Distrib(generator)};
        const int rum{Rum_Distrib(generator)};
        if(S.free(r)){
            if(r.y!=H-1-r.y){
                S.B.push_back({S.entityId++,vec{r.x,H-1-r.y},rum});
            }
            S.B.push_back({S.entityId++,r,rum});
        }
    }
    int winner{Play_Game(Bot_Names,S)};
    if(player_swap){
        return winner==-1?-1:winner==0?1:0;
    }
    else{
        return winner;
    }
}

void StopArena(const int signum){
    stop=true;
}

int main(int argc,char **argv){
    if(argc<3){
        cerr << "Program takes 2 inputs, the names of the AIs fighting each other" << endl;
        return 0;
    }
    int N_Threads{1};
    if(argc>=4){//Optional N_Threads parameter
        N_Threads=min(2*omp_get_num_procs(),max(1,atoi(argv[3])));
        cerr << "Running " << N_Threads << " arena threads" << endl;
    }
    array<string,N> Bot_Names;
    for(int i=0;i<2;++i){
        Bot_Names[i]=argv[i+1];
    }
    cout << "Testing AI " << Bot_Names[0];
    for(int i=1;i<N;++i){
        cerr << " vs " << Bot_Names[i];
    }
    cerr << endl;
    for(int i=0;i<N;++i){//Check that AI binaries are present
        ifstream Test{Bot_Names[i].c_str()};
        if(!Test){
            cerr << Bot_Names[i] << " couldn't be found" << endl;
            return 0;
        }
        Test.close();
    }
    signal(SIGTERM,StopArena);//Register SIGTERM signal handler so the arena can cleanup when you kill it
    signal(SIGPIPE,SIG_IGN);//Ignore SIGPIPE to avoid the arena crashing when an AI crashes
    int games{0},draws{0};
    array<double,2> points{0,0};
    #pragma omp parallel num_threads(N_Threads) shared(games,points,Bot_Names)
    while(!stop){
        int winner{Play_Round(Bot_Names)};
        if(winner==-1){//Draw
            #pragma omp atomic
            ++draws;
            #pragma omp atomic
            points[0]+=0.5;
            #pragma omp atomic
            points[1]+=0.5;
        }
        else{//Win
            ++points[winner];
        }
        #pragma omp atomic
        ++games;
        double p{static_cast<double>(points[0])/games};
        double sigma{sqrt(p*(1-p)/games)};
        double better{0.5+0.5*erf((p-0.5)/(sqrt(2)*sigma))};
        #pragma omp critical
        cout << "Wins:" << setprecision(4) << 100*p << "+-" << 100*sigma << "% Rounds:" << games << " Draws:" << draws << " " << better*100 << "% chance that " << Bot_Names[0] << " is better" << endl;
    }
}