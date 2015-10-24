 #include "MyStrategy.h"

#define _USE_MATH_DEFINES
#include <cmath>
#include <climits>
#include <cstring>
#include <limits>
#include <algorithm>
#include <list>
#include <map>

#include <iostream>  // DEBUG
#include <iomanip>  // DEBUG
#include <ctime>  // DEBUG

using namespace model;
using namespace std;



inline double sqr(double x)
{
    return x * x;
}

inline double rem(double x, double y)
{
    x /= y;
    return y * (x - floor(x));
}


struct Vec2D
{
    double x, y;

    Vec2D()
    {
    }

    Vec2D(const Vec2D &v) : x(v.x), y(v.y)
    {
    }

    Vec2D(double x_, double y_) : x(x_), y(y_)
    {
    }

    Vec2D &operator = (const Vec2D &v)
    {
        x = v.x;  y = v.y;  return *this;
    }

    Vec2D operator + (const Vec2D &v) const
    {
        return Vec2D(x + v.x, y + v.y);
    }

    Vec2D &operator += (const Vec2D &v)
    {
        x += v.x;  y += v.y;  return *this;
    }

    Vec2D operator - (const Vec2D &v) const
    {
        return Vec2D(x - v.x, y - v.y);
    }

    Vec2D &operator -= (const Vec2D &v)
    {
        x -= v.x;  y -= v.y;  return *this;
    }

    Vec2D operator - () const
    {
        return Vec2D(-x, -y);
    }

    Vec2D operator * (double a) const
    {
        return Vec2D(a * x, a * y);
    }

    Vec2D &operator *= (double a)
    {
        x *= a;  y *= a;  return *this;
    }

    double operator * (const Vec2D &v) const
    {
        return x * v.x + y * v.y;
    }

    Vec2D operator / (double a) const
    {
        return (*this) * (1 / a);
    }

    Vec2D operator /= (double a)
    {
        return (*this) *= (1 / a);
    }

    Vec2D operator ~ () const
    {
        return Vec2D(y, -x);
    }

    double operator % (const Vec2D &v) const
    {
        return *this * ~v;
    }

    double sqr() const
    {
        return x * x + y * y;
    }

    double len() const
    {
        return std::sqrt(x * x + y * y);
    }
};

inline Vec2D operator * (double a, const Vec2D &v)
{
    return v * a;
}

inline Vec2D normalize(const Vec2D &v)
{
    return v / v.len();
}

inline Vec2D sincos(double angle)
{
    return Vec2D(cos(angle), sin(angle));
}

inline Vec2D conj(const Vec2D &v)
{
    return Vec2D(v.x, -v.y);
}


struct Quad
{
    Vec2D pos, dir;
    double half_w, half_h;

    Quad()
    {
    }

    Quad(const Vec2D &pos_, const Vec2D &dir_, double hw, double hh) :
        pos(pos_), dir(dir_), half_w(hw), half_h(hh)
    {
    }

    Quad(const Unit &unit) : pos(unit.x(), unit.y()),
        dir(sincos(unit.angle())), half_w(unit.width() / 2), half_h(unit.height() / 2)
    {
    }

    Quad(const Vec2D &start, const Vec2D &delta, double size) : half_h(size / 2)
    {
        dir = delta / 2;  half_w = dir.len();  pos = start + dir;  dir /= half_w;
    }

    Quad move(const Vec2D &pt) const
    {
        return Quad(pt, dir, half_w, half_h);
    }

    bool checkPoint(const Vec2D &pt, double rad = 0) const
    {
        Vec2D dr = pt - pos;
        return abs(dr * dir) < half_w + rad && abs(dr % dir) < half_h + rad;
    }

    bool cross(const Quad &q) const
    {
        Vec2D dr = pos - q.pos;
        //if(dr.sqr() > sqr(half_w + half_h + q.half_w + q.half_h))return false;

        double dot = abs(dir * q.dir), cross = abs(dir % q.dir);
        if(!(abs(dr * dir) < half_w + q.half_w * dot + q.half_h * cross))return false;
        if(!(abs(dr % dir) < half_h + q.half_h * dot + q.half_w * cross))return false;
        if(!(abs(dr * q.dir) < q.half_w + half_w * dot + half_h * cross))return false;
        if(!(abs(dr % q.dir) < q.half_h + half_h * dot + half_w * cross))return false;
        return true;
    }

    void crossRange(const Quad &q, const Vec2D &delta, double &t_min, double &t_max) const
    {
        Vec2D dr = pos - q.pos;
        double center1 = dr * dir, center2 = dr % dir;
        double center3 = dr * q.dir, center4 = dr % q.dir;
        double dot = abs(dir * q.dir), cross = abs(dir % q.dir);
        double delta1 = half_w + q.half_w * dot + q.half_h * cross;
        double delta2 = half_h + q.half_h * dot + q.half_w * cross;
        double delta3 = q.half_w + half_w * dot + half_h * cross;
        double delta4 = q.half_h + half_h * dot + half_w * cross;

        double mul1 = 1 / (delta * dir), mul2 = 1 / (delta % dir);
        double mul3 = 1 / (delta * q.dir), mul4 = 1 / (delta % q.dir);
        if(mul1 < 0)delta1 = -delta1;  if(mul2 < 0)delta2 = -delta2;
        if(mul3 < 0)delta3 = -delta3;  if(mul4 < 0)delta4 = -delta4;
        t_min = max(max((center1 - delta1) * mul1, (center2 - delta2) * mul2),
                    max((center3 - delta3) * mul3, (center4 - delta4) * mul4));
        t_max = min(min((center1 + delta1) * mul1, (center2 + delta2) * mul2),
                    min((center3 + delta3) * mul3, (center4 + delta4) * mul4));
    }

    void crossLine(const Vec2D &start, const Vec2D &delta, double &t_min, double &t_max) const
    {
        Vec2D dr = pos - start;
        double center1 = dr * dir, center2 = dr % dir;
        double delta1 = half_w, delta2 = half_h;

        double mul1 = 1 / (delta * dir), mul2 = 1 / (delta % dir);
        if(mul1 < 0)delta1 = -delta1;  if(mul2 < 0)delta2 = -delta2;
        t_min = max((center1 - delta1) * mul1, (center2 - delta2) * mul2);
        t_max = min((center1 + delta1) * mul1, (center2 + delta2) * mul2);
    }
};



struct GlobalParams
{
    double crew_danger_att, hull_danger_att, ang_spd_account;
    double medkit_score, repkit_score, ammo_score;
    double obst_danger, phys_lookahead, rot_bonus;
    double tg_border, tg_lookahead;
    double tg_prem_danger, tg_ang_att, tg_base_score;
    double tg_prem_bonus, tg_prem_offs, tg_fire_thr;
    double aggr_factor, aggr_lookahead;
    double team_force, team_dist;
    double dng_ang_att, dng_lookahead;
    double prem_danger, hit_danger;

#ifdef OPTIMIZING

    GlobalParams()
    {
        static const unsigned long long flag = 0x0123456789ABCDEF;

        unsigned long long buf;
        cin.read(reinterpret_cast<char *>(&buf), sizeof(buf));
        if(buf == flag)
        {
            cin.read(reinterpret_cast<char *>(this), sizeof(*this));
            cin.read(reinterpret_cast<char *>(&buf), sizeof(buf));
            if(buf == flag)return;
        }
        cout << "Invalid input!!!" << endl;  exit(-1);
    }

#else

    GlobalParams()
    {
        /*crew_danger_att = 0.4;
        hull_danger_att = 0.3;
        ang_spd_account = 0.1;
        medkit_score = 2.5;
        repkit_score = 0.4;
        ammo_score = 0.2;
        obst_danger = 30;
        phys_lookahead = 50;
        rot_bonus = 10;
        tg_border = 8;
        tg_lookahead = 600;
        tg_prem_danger = 0;
        tg_ang_att = 0.07;
        tg_base_score = 0.8;
        tg_prem_bonus = 3;
        tg_prem_offs = 2;
        tg_fire_thr = 0.25;
        aggr_factor = 1.2;
        aggr_lookahead = 30000;
        team_force = 0.08;
        team_dist = 250;
        dng_ang_att = 6;
        dng_lookahead = 100;
        prem_danger = 0.5;
        hit_danger = 4000;*/

        /*crew_danger_att = 0.7;
        hull_danger_att = 0.15;
        ang_spd_account = 0.5;
        medkit_score = 5;
        repkit_score = 0.3;
        ammo_score = 1;
        obst_danger = 8;
        phys_lookahead = 70;
        rot_bonus = 2;
        tg_border = 8;
        tg_lookahead = 200;
        tg_prem_danger = 0.04;
        tg_ang_att = 0.01;
        tg_base_score = 1;
        tg_prem_bonus = 20;
        tg_prem_offs = 10;
        tg_fire_thr = 0.3;
        aggr_factor = 0.2;
        aggr_lookahead = 2000;
        team_force = 0.08;
        team_dist = 200;
        dng_ang_att = 20;
        dng_lookahead = 50;
        prem_danger = 0.1;
        hit_danger = 200;*/

        crew_danger_att = 0.7;
        hull_danger_att = 0.15;
        ang_spd_account = 0.5;
        medkit_score = 5;
        repkit_score = 0.3;
        ammo_score = 1;
        obst_danger = 8;
        phys_lookahead = 70;
        rot_bonus = 2;
        tg_border = 8;
        tg_lookahead = 200;
        tg_prem_danger = 0.04;
        tg_ang_att = 0.01;
        tg_base_score = 1;
        tg_prem_bonus = 20;
        tg_prem_offs = 10;
        tg_fire_thr = 0.3;
        aggr_factor = 2;
        aggr_lookahead = 2000;
        team_force = 0.08;
        team_dist = 200;
        dng_ang_att = 20;
        dng_lookahead = 50;
        prem_danger = 0.1;
        hit_danger = 200;
    }

#endif

};

const GlobalParams prm;



struct ShellInfo
{
    double frict, v0, mul, range, score;
    FireType fire;

    ShellInfo(double frict_, double v0_, FireType fire_, double score_) :
        frict(frict_), v0(v0_), mul(1 / log(1 - frict_)), range(v0_ / frict_), score(score_), fire(fire_)
    {
    }
};

const ShellInfo shell_info[] =
{
    ShellInfo(0.005, 50 / 3.0, REGULAR_FIRE, 10),
    ShellInfo(0.010, 40 / 3.0, PREMIUM_FIRE, 20)
};



inline double crew_danger(const Tank &tank)
{
    return 1 - prm.crew_danger_att * tank.crew_health() / tank.crew_max_health();
}

inline double hull_danger(const Tank &tank)
{
    return 1 - prm.hull_danger_att * tank.hull_durability() / tank.hull_max_durability();
}

struct FriendRef
{
    Vec2D pos, turret;
    double ang_spd, gun_len, gun_angle;
    double danger;  bool premium;  size_t quad_index;
    long long id;  int prev_dir;

    FriendRef(const Tank &tank, size_t index, int prev) : pos(tank.x(), tank.y()),
        ang_spd(tank.angular_speed()), gun_len(tank.virtual_gun_length()),
        gun_angle(tank.angle() + tank.turret_relative_angle()),
        danger(max(crew_danger(tank), hull_danger(tank))),
        premium(tank.premium_shell_count()), quad_index(index),
        id(tank.id()), prev_dir(prev)
    {
        turret = sincos(gun_angle);
    }
};


struct BonusRef
{
    Vec2D pos;
    BonusType type;

    static void calcScore(const Tank &tank, double score[3])
    {
        score[MEDIKIT] = prm.medkit_score * crew_danger(tank) *
            min(1.0, (tank.crew_max_health() - tank.crew_health()) / 35.0);
        score[REPAIR_KIT] = prm.repkit_score * hull_danger(tank) *
            min(1.0, (tank.hull_max_durability() - tank.hull_durability()) / 50.0);
        score[AMMO_CRATE] = prm.ammo_score;
    }

    BonusRef(const Bonus &bonus) : pos(bonus.x(), bonus.y()), type(bonus.type())
    {
    }
};


struct Action
{
    double force, moment;

    Action()
    {
    }

    Action(const Tank &tank, double move_l, double move_r)
    {
        if(move_l < 0)move_l *= tank.engine_rear_power_factor();
        if(move_r < 0)move_r *= tank.engine_rear_power_factor();
        double mul = 0.04947917 * (1 + tank.crew_health() / double(tank.crew_max_health()));
        force = (move_l + move_r) * mul;  moment = 0.004229904 * (move_l - move_r) * mul;
    }
};

struct State : public Quad
{
    double angle, ang_spd;
    Vec2D spd;

    State()
    {
    }

    State(const Unit &unit) : Quad(unit),
        angle(unit.angle()), ang_spd(unit.angular_speed()),
        spd(unit.speed_x(), unit.speed_y())
    {
    }

    void bounce(const Vec2D &r, const Vec2D &norm, double depth)
    {
        double rt = r % norm, ri = rt / 975, w = 1 / (1 + rt * ri);
        double pr = -1.325 * min(0.0, spd * norm + 0.51 * rt * ang_spd) * w;
        double pp = 0.8 * max(0.0, depth - 0.01) * w;
        spd += pr * norm;  ang_spd += pr * ri;
        pos += pp * norm;  angle += pp * ri;
    }

    void checkBounds(const Vec2D &size)
    {
        double w = size.x / 2, h = size.y / 2;
        Vec2D rw = half_w * dir, rh = half_h * ~dir;
        Vec2D r1 = rw + rh, r2 = rw - rh;

        double depth = abs(pos.x - w) + max(abs(r1.x), abs(r2.x)) - w;
        if(depth > 0)
        {
            Vec2D norm(pos.x < w ? 1 : -1, 0);
            Vec2D &r = abs(r1.x) > abs(r2.x) ? r1 : r2;
            bounce((r.x < 0 ? norm.x : -norm.x) * r, norm, depth);
        }
        depth = abs(pos.y - h) + max(abs(r1.y), abs(r2.y)) - h;
        if(depth > 0)
        {
            Vec2D norm(0, pos.y < h ? 1 : -1);
            Vec2D &r = abs(r1.y) > abs(r2.y) ? r1 : r2;
            bounce((r.y < 0 ? norm.y : -norm.y) * r, norm, depth);
        }
    }

    void advance(const Action &act, const Vec2D &size)
    {
        spd += act.force * dir - 0.05 * spd;
        ang_spd += act.moment - 0.02051282 * ang_spd;

        checkBounds(size);
        pos += spd;  dir = sincos(angle += ang_spd);
    }
};


struct ShellRef : public Quad
{
    Vec2D spd;
    double frict, score;

    ShellRef()
    {
    }

    ShellRef(const Vec2D &pos, const Vec2D &dir, double gun_len, ShellType type) :
        Quad(pos + dir * gun_len, dir, 11.25, 3.75), spd(shell_info[type].v0 * dir),
        frict(shell_info[type].frict), score(shell_info[type].score)

    {
    }

    ShellRef(const Shell &shell) : Quad(shell), spd(shell.speed_x(), shell.speed_y()),
        frict(shell_info[shell.type()].frict), score(shell_info[shell.type()].score)
    {
    }

    void advance()
    {
        spd -= frict * spd;  pos += spd;
    }
};


struct TankInfo
{
    double force, moment, damp, rot_damp;

    TankInfo(double force_, double moment_, double damp_, double rot_damp_) :
        force(force_), moment(moment_), damp(damp_), rot_damp(rot_damp_)
    {
    }
};

const TankInfo tank_info[] =
{
    TankInfo(0.19791669, 0.00020929222, 1.0 / 20, 0.02051282),  // MEDIUM
    TankInfo(0.11510416, 0.00008385862, 1.0 / 40, 0.01441441),  // HEAVY
    TankInfo(0.08950617, 0.00006365248, 1.0 / 30, 0.01394335)   // TANK_DESTROYER
};


struct ScoreElem
{
    double pos, val;

    ScoreElem()
    {
    }

    ScoreElem(double pos_, double val_) : pos(pos_), val(val_)
    {
    }
};

struct ScoreRange : public list<ScoreElem>
{
    ScoreRange()
    {
        push_back(ScoreElem(-numeric_limits<double>::infinity(), 0));
        push_back(ScoreElem(numeric_limits<double>::infinity(), 0));
    }

    static double timeMerge(double prev, double cur)
    {
        return prev == 0 ? cur : prev;
    }

    static double addMerge(double prev, double cur)
    {
        return prev + cur;
    }

    template<double (*func)(double, double), typename Iter> void merge(Iter beg, Iter end)
    {
        iterator ptr = begin();
        double prev = 0, cur = 0, res = 0;  ++ptr;
        for(; beg != end; ++beg)
        {
            while(ptr->pos < beg->pos)
            {
                double val = func(prev = ptr->val, cur);
                iterator old = ptr++;
                if(val == res)erase(old);
                else old->val = res = val;
            }
            cur = beg->val;
            if(ptr->pos == beg->pos)
            {
                double val = func(prev = ptr->val, cur);
                iterator old = ptr++;
                if(val == res)erase(old);
                else old->val = res = val;
            }
            else
            {
                double val = func(prev, cur);
                if(val != res)insert(ptr, ScoreElem(beg->pos, res = val));
            }
        }
    }

    void merge(ScoreElem *elem, size_t n)
    {
        merge<timeMerge>(elem, elem + n);
    }

    void add(const ScoreRange &rng)
    {
        const_iterator first = rng.begin(), last = rng.end();
        if(++first != --last)merge<addMerge>(first, last);
    }

    double integrate() const
    {
        const_iterator ptr = begin(), last = end();  if(++ptr == --last)return 0;
        for(double res = 0;;)
        {
            const_iterator old = ptr;  if(++ptr == last)return res;
            res += sqrt(sqrt(old->val)) * (ptr->pos - old->pos);
        }
    }

    void print() const
    {
        const_iterator ptr = begin(), last = end();  cout << ptr->val;
        for(++ptr, --last; ptr != last; ++ptr)cout << " (" << ptr->pos << ") " << ptr->val;
        cout << endl;
    }
};


struct Target
{
    struct Prediction
    {
        Vec2D pos, delta, dir;
        double min, max;
    };


    static const int max_pred = 256;
    static const double dmul;


    double half_w, half_h;
    vector<Prediction> pred;
    double delta_min, delta_max;
    ScoreRange base_range;
    double score_offset;

    Vec2D turret;
    double gun_len, score_mul;
    int fire_time;  bool premium;
    size_t quad_index;

    Target(const Tank &tank, size_t index) :
        half_w(tank.width() / 2 - prm.tg_border),
        half_h(tank.height() / 2 - prm.tg_border),
        turret(sincos(tank.angle() + tank.turret_relative_angle())),
        gun_len(tank.virtual_gun_length()),
        score_mul(sqr(max(crew_danger(tank), hull_danger(tank)))),
        fire_time(tank.remaining_reloading_time()),
        premium(tank.premium_shell_count()), quad_index(index)
    {
    }

    void generate(const Tank &tank);
    void calcRange(ShellRef shell, int step, int total, ScoreRange &range) const;

    void processShell(const ShellRef &shell)
    {
        ScoreRange range;  calcRange(shell, 0, max_pred, range);  base_range.add(range);
    }

    void updateBase()
    {
        score_offset = sqr(sqr(base_range.integrate() / (delta_max - delta_min)));
    }

    double calcScore(const ShellRef &shell, int step, int total) const
    {
        ScoreRange range;  calcRange(shell, step, total, range);  range.add(base_range);
        return sqr(sqr(range.integrate() / (delta_max - delta_min))) - score_offset;
    }
};

const double Target::dmul = exp(-1 / prm.tg_lookahead);


struct GunMove
{
    double gun_move;
    FireType fire_type;
};

struct DangerField
{
    static const double h, dmul, max_bonus;

    static int cur_tick;
    static vector<Target> target;
    static vector<FriendRef> fref;
    static vector<ShellRef> sref;
    static vector<Vec2D> shell_pos;
    static vector<BonusRef> bref;
    static vector<Quad> quad;
    static size_t block_count;

    static Vec2D size, offset;
    static size_t width, height;


    size_t cur, quad_index;
    vector<double> danger;
    double min_danger;

    vector<Action> act;
    double bonus_score[3];
    double tg_angle, gun_spd;
    int fire_time;

    double gun_spd_p, gun_spd_n, gun_move;
    FireType fire_type;


    static void init(const World &world);
    DangerField(const World &world, const Tank &tank);

    static bool checkRay(const Vec2D &start, const Vec2D &delta, size_t skip1, size_t skip2 = -1);
    static double checkRay(const ShellRef &shell, size_t skip1, size_t skip2 = -1);
    void blur();

    double sampleDanger(const Vec2D &pos);
    double hitDanger(const State &state, size_t index, int step);
    double samplePhys(State state, size_t index, const size_t *max_act,
        double mul, double sum, vector<bool> flag, double best, int step = 0);
    size_t samplePhys(const Tank &tank, const double move[][2], const size_t *max_move);
    double checkTarget(const Target &tank, double angle, double &best_angle, GunMove &res, double best);

    void print();
};

const double DangerField::h = 16;  // blur() dependent
const double DangerField::dmul = exp(-1 / prm.phys_lookahead);
const double DangerField::max_bonus = prm.medkit_score + prm.repkit_score + prm.ammo_score;

int DangerField::cur_tick = -1;
vector<Target> DangerField::target;
vector<FriendRef> DangerField::fref;
vector<ShellRef> DangerField::sref;
vector<Vec2D> DangerField::shell_pos;
vector<BonusRef> DangerField::bref;
vector<Quad> DangerField::quad;
size_t DangerField::block_count;

Vec2D DangerField::size, DangerField::offset;
size_t DangerField::width, DangerField::height;


inline double shellFlyTime(double dist, ShellType type)
{
    if(!(dist < shell_info[type].range))return numeric_limits<double>::infinity();
    return shell_info[type].mul * log(1 - dist / shell_info[type].range);
}

void DangerField::init(const World &world)
{
    if(world.tick() == cur_tick)return;
    //cout << cur_tick << endl;
    cur_tick = world.tick();

    size = Vec2D(world.width(), world.height());
    width = size_t(floor(size.x / h + 0.5)) + 6;
    height = size_t(floor(size.y / h + 0.5)) + 6;
    offset = (size - Vec2D(width - 1, height - 1) * h) / 2;

    vector<Tank> tanks = world.tanks();
    vector<Shell> shells = world.shells();
    vector<Bonus> bonuses = world.bonuses();
    vector<Obstacle> obstacles = world.obstacles();

    quad.clear();
    for(vector<Obstacle>::iterator ptr = obstacles.begin(); ptr != obstacles.end(); ++ptr)
        quad.push_back(*ptr);

    map<long long, int> prev_dir;
    for(vector<FriendRef>::iterator ptr = fref.begin(); ptr != fref.end(); ++ptr)
        prev_dir[ptr->id] = ptr->prev_dir;

    target.clear();  fref.clear();
    for(vector<Tank>::iterator ptr = tanks.begin(); ptr != tanks.end(); ++ptr)
    {
        if(ptr->crew_health() && ptr->hull_durability())
            if(ptr->teammate())fref.push_back(FriendRef(*ptr, quad.size(), prev_dir[ptr->id()]));
            else target.push_back(Target(*ptr, quad.size()));
        quad.push_back(*ptr);
    }
    block_count = quad.size();

    sref.clear();  shell_pos.clear();
    for(vector<Shell>::iterator ptr = shells.begin(); ptr != shells.end(); ++ptr)
    {
        sref.push_back(*ptr);  shell_pos.push_back(sref[sref.size() - 1].pos);
    }

    bref.clear();
    for(vector<Bonus>::iterator ptr = bonuses.begin(); ptr != bonuses.end(); ++ptr)
    {
        quad.push_back(*ptr);  bref.push_back(*ptr);
    }

    size_t index = 0;
    for(vector<Tank>::iterator ptr = tanks.begin(); ptr != tanks.end(); ++ptr)
        if(!ptr->teammate() && ptr->crew_health() && ptr->hull_durability())
            target[index++].generate(*ptr);

    for(size_t i = 0; i < target.size(); i++)
    {
        double mul = 0;
        for(size_t j = 0; j < fref.size(); j++)
        {
            Vec2D delta = target[i].pred[0].pos - fref[j].pos;
            double dist = delta.len(), cos_turret = target[i].turret * delta / dist;

            double val = 1 - dist / shell_info[REGULAR].range;
            if(target[i].premium)val = max(val, (prm.tg_prem_danger + 1) * (1 - dist / shell_info[PREMIUM].range));
            val *= exp(-prm.tg_ang_att * (1 + cos_turret)) * fref[j].danger;  mul = max(mul, val);
        }
        target[i].score_mul *= mul + prm.tg_base_score;

        for(size_t j = 0; j < sref.size(); j++)target[i].processShell(sref[j]);
        target[i].updateBase();
    }
}

DangerField::DangerField(const World &world, const Tank &tank) : gun_move(0), fire_type(NONE)
{
    init(world);
    for(cur = 0;; cur++)
        if(cur >= fref.size())
        {
            cur = -1;  return;
        }
        else if(fref[cur].id == tank.id())break;
    quad_index = fref[cur].quad_index;

    danger.resize(width * height);  vector<double> aggr(width * height);

    fire_time = tank.remaining_reloading_time();
    double aggr_mul = prm.aggr_factor * exp(-fire_time / prm.aggr_lookahead) * fref.size() / target.size();
    for(size_t j = 0, k = 0; j < height; j++)for(size_t i = 0; i < width; i++, k++)
    {
        Vec2D start = offset + Vec2D(i, j) * h;
        if(!(start.x > 0 && start.x < size.x && start.y > 0 && start.y < size.y))
        {
            danger[k] = prm.obst_danger;  continue;
        }

        for(size_t i = 0; i < block_count; i++)
            if(i != quad_index && quad[i].checkPoint(start))
            {
                danger[k] += prm.obst_danger;  break;
            }

        for(size_t i = 0; i < fref.size(); i++)if(i != cur)
            danger[k] += prm.team_force * sqr(2 / (1 + (fref[i].pos - start).sqr() / sqr(prm.team_dist)) - 1);

        for(vector<Target>::iterator ptr = target.begin(); ptr != target.end(); ++ptr)
        {
            Vec2D delta = ptr->pred[0].pos - start;
            if(!checkRay(start, delta, quad_index, ptr->quad_index))continue;
            double dist = delta.len(), w = exp(-prm.dng_ang_att * (1 + ptr->turret * delta / dist));

            dist = max(0.0, dist - ptr->gun_len);
            w *= sqr(sqr(1 - dist / shell_info[REGULAR].range));
            double time = ptr->fire_time + shellFlyTime(dist, REGULAR);
            danger[k] += w * exp(-time / prm.dng_lookahead) * fref[cur].danger * (ptr->premium ? prm.prem_danger + 1 : 1);
            aggr[k] = max(aggr[k], (1 - dist / shell_info[REGULAR].range) * ptr->score_mul * aggr_mul);
        }
    }

    blur();  min_danger = prm.obst_danger;
    for(size_t k = 0; k < width * height; k++)min_danger = min(min_danger, danger[k] -= aggr[k]);
    //if(!cur)print();

    double best_target = 0;
    gun_spd_p = max(1e-9, tank.turret_turn_speed() + prm.ang_spd_account * tank.angular_speed());
    gun_spd_n = max(1e-9, tank.turret_turn_speed() - prm.ang_spd_account * tank.angular_speed());
    for(vector<Target>::iterator ptr = target.begin(); ptr != target.end(); ++ptr)
    {
        Vec2D delta = ptr->pred[0].pos - fref[cur].pos;  GunMove res;
        double angle = atan2(delta.y, delta.x), next = angle, da = M_PI / 18;
        double best = checkTarget(*ptr, angle, next, res, 0), cur;
        for(int i = 0; i < 4; i++)
        {
            best = checkTarget(*ptr, angle - da, next, res, best);
            best = checkTarget(*ptr, angle + da, next, res, best);
            best = checkTarget(*ptr, angle - 3 * da, next, res, best);
            best = checkTarget(*ptr, angle + 3 * da, next, res, best);
            angle = next;  da /= 2;
        }
        if(!fire_time)best = checkTarget(*ptr, fref[cur].gun_angle, next, res, best);
        //if(best != 0 && res.fire_type)cout << "Firing, score: " << best << endl;
        best *= ptr->score_mul;

        if(!(best > best_target))continue;  best_target = best;
        gun_move = res.gun_move;  fire_type = res.fire_type;
    }
}

bool DangerField::checkRay(const Vec2D &start, const Vec2D &delta, size_t skip1, size_t skip2)
{
    Quad ray(start, delta, 7.5);
    size_t list[] = {min(skip1, skip2), max(skip1, skip2), -1}, *skip = list;
    for(size_t i = 0; i < quad.size(); i++)
        if(i == *skip)skip++;
        else if(quad[i].cross(ray))return false;
    return true;
}

double DangerField::checkRay(const ShellRef &shell, size_t skip1, size_t skip2)
{
    double res = numeric_limits<double>::infinity();
    size_t list[] = {min(skip1, skip2), max(skip1, skip2), -1}, *skip = list;
    for(size_t i = 0; i < quad.size(); i++)
        if(i != *skip)
        {
            double t_min, t_max;
            quad[i].crossRange(shell, shell.dir, t_min, t_max);
            if(t_min < t_max && t_max > 0)res = min(res, t_min);
        }
        else skip++;
    return max(0.0, res);
}

void DangerField::blur()  // blur radius ~ 3.5 * h
{
    vector<double> buffer(danger.size() + 3 * width);

    size_t offs = 2 * width + 2, k = 0;
    for(; k < 5 * width + 1; k++)buffer[k] = prm.obst_danger;
    for(; k < danger.size() - width - 1; k++)
    {
        size_t pos = k - offs;
        buffer[k] = (danger[pos] + danger[pos + 1] + danger[pos + 2] + danger[pos + 3] + danger[pos + 4]) / 5;
    }
    for(; k < danger.size() + 3 * width; k++)buffer[k] = prm.obst_danger;

    for(k = width + 1; k < danger.size() - width - 1; k++)
    {
        size_t pos = k;  double res = buffer[k];
        pos += width;  res += buffer[pos];
        pos += width;  res += buffer[pos];
        pos += width;  res += buffer[pos];
        pos += width;  res += buffer[pos];
        buffer[k] = res / 5;
    }

    static const double w1 = 0.8, w2 = 0.3;
    static const double c0 = 1 / (29 + 8 * (w1 + w2)), c1 = w1 * c0, c2 = w2 * c0;
    static const double cc = 25 * c0, ch = 2 * c0 + 4 * (c1 + c2);

    for(k = 0; k < 3 * width + 2; k++)
    {
        buffer[k] = cc * buffer[k] + ch * prm.obst_danger + c0 * (danger[k + 3 * width] + danger[k + 3]) +
            c1 * (danger[k + 3 * width - 1] + danger[k + 3 * width + 1] + danger[k + width - 3] + danger[k + width + 3]) +
            c2 * (danger[k + 3 * width - 2] + danger[k + 3 * width + 2] + danger[k + 2 * width - 3] + danger[k + 2 * width + 3]);
    }
    for(; k < danger.size() - 3 * width - 2; k++)
    {
        buffer[k] = cc * buffer[k] + c0 * (danger[k - 3 * width] + danger[k + 3 * width] + danger[k - 3] + danger[k + 3]) +
            c1 * (danger[k - 3 * width - 1] + danger[k - 3 * width + 1] + danger[k + 3 * width - 1] + danger[k + 3 * width + 1] +
                danger[k - width - 3] + danger[k - width + 3] + danger[k + width - 3] + danger[k + width + 3]) +
            c2 * (danger[k - 3 * width - 2] + danger[k - 3 * width + 2] + danger[k + 3 * width - 2] + danger[k + 3 * width + 2] +
                danger[k - 2 * width - 3] + danger[k - 2 * width + 3] + danger[k + 2 * width - 3] + danger[k + 2 * width + 3]);
    }
    for(; k < danger.size(); k++)
    {
        buffer[k] = cc * buffer[k] + ch * prm.obst_danger + c0 * (danger[k - 3 * width] + danger[k - 3]) +
            c1 * (danger[k - 3 * width - 1] + danger[k - 3 * width + 1] + danger[k - width - 3] + danger[k - width + 3]) +
            c2 * (danger[k - 3 * width - 2] + danger[k - 3 * width + 2] + danger[k - 2 * width - 3] + danger[k - 2 * width + 3]);
    }

    buffer.resize(danger.size());  danger.swap(buffer);
}

double DangerField::sampleDanger(const Vec2D &pos)
{
    Vec2D index = (pos - offset) / h;
    size_t i = size_t(floor(index.x)), j = size_t(floor(index.y));
    if(i >= width - 1 || j >= height - 1)return prm.obst_danger;

    index -= Vec2D(i, j);  size_t k = i + j * width;
    double up = danger[k] + (danger[k + 1] - danger[k]) * index.x;  k += width;
    double dn = danger[k] + (danger[k + 1] - danger[k]) * index.x;
    return up + (dn - up) * index.y;
}

double DangerField::hitDanger(const State &state, size_t index, int step)
{
    size_t pindex = step * sref.size() + index;
    if(!checkRay(shell_pos[pindex], shell_pos[pindex] - shell_pos[index], quad_index))return 0;

    double dot = sref[index].dir * state.dir, cross = sref[index].dir % state.dir;
    double w = dot > 0 ? -state.half_w : state.half_w, h = cross > 0 ? -state.half_h : state.half_h;
    double offs = (state.pos + w * state.dir + h * ~state.dir - shell_pos[pindex]) % sref[index].dir;
    if(dot * cross > 0)offs = -offs;

    static const double back = 1 / 1.0, side = 1 / 1.5, front = 1 / 1.75;

    double mul = prm.hit_danger * prm.obst_danger * sref[index].score;
    mul *= (shell_pos[pindex] - shell_pos[pindex - sref.size()]).len();
    if(offs < -sref[index].half_h)return side * mul * sqr(cross);
    if(offs > sref[index].half_h)return (dot > 0 ? back : front) * mul * sqr(dot);
    return (dot > 0 ? back : side) * mul;
}

double DangerField::samplePhys(State state, size_t index, const size_t *max_act,
    double mul, double sum, vector<bool> flag, double best, int step)
{
    for(step++;; step++)
    {
        state.advance(act[index], size);  double dng = sampleDanger(state.pos);
        //if(!index && !(state.spd.sqr() > sqr(0.05 * h)) || !(mul > 1e-3))return min(best, sum + dng * mul);
        if(!index && step > 64 || !(mul > 1e-3))return min(best, sum + dng * mul);  // TODO: shell stop
        sum += dng * mul * (1 - dmul);

        if(step >= fire_time && flag[0] &&
            abs(rem(state.angle - tg_angle + M_PI, 2 * M_PI) - M_PI) < step * gun_spd)
        {
            sum -= prm.rot_bonus * mul;  flag[0] = false;
        }

        size_t fpos = 1;
        for(size_t j = 0; j < bref.size(); j++)
            if(flag[fpos + j] && state.checkPoint(bref[j].pos))
            {
                sum -= bonus_score[bref[j].type] * mul;  flag[fpos + j] = false;
            }

        size_t offs = step * sref.size();  fpos += bref.size();
        while(shell_pos.size() < offs + sref.size())
            for(size_t j = 0; j < sref.size(); j++)
            {
                sref[j].advance();  shell_pos.push_back(sref[j].pos);
            }
        for(size_t j = 0; j < sref.size(); j++)
            if(flag[fpos + j] && state.cross(sref[j].move(shell_pos[offs + j])))
            {
                sum += hitDanger(state, j, step) * mul;  flag[fpos + j] = false;
            }

        mul *= dmul;
        double min_total = min_danger - (flag[0] ? prm.rot_bonus : 0) - max_bonus;
        if(!(sum + min_total * mul < best))return best;

        if(index && !(step % 32))for(size_t i = 0; i < *max_act; i++)if(i != index)
            best = samplePhys(state, i, max_act + 1, mul, sum, flag, best, step);
    }
}

size_t DangerField::samplePhys(const Tank &tank, const double move[][2], const size_t *max_move)
{
    size_t move_count = 1;
    for(const size_t *ptr = max_move; *ptr > 1; ptr++)move_count = max(move_count, *ptr);

    act.resize(move_count);
    for(size_t i = 0; i < move_count; i++)act[i] = Action(tank, move[i][0], move[i][1]);

    BonusRef::calcScore(tank, bonus_score);
    tg_angle = tank.angle() + gun_move;
    gun_spd = tank.turret_turn_speed();

    State state(tank);
    double dng = sampleDanger(state.pos);
    double mul = dmul, sum = dng * (1 - mul);
    vector<bool> flag(bref.size() + sref.size() + 1, true);
    flag[0] = fire_time;

    double best = numeric_limits<double>::infinity();
    size_t dir = 0, prev = fref[cur].prev_dir;
    if(prev < move_count)
    {
        best = samplePhys(state, prev, max_move + 1, mul, sum, flag, best);
        dir = prev;
    }
    for(size_t i = 0; *max_move > 1; max_move++)
        for(; i < *max_move; i++)if(i != prev)
        {
            double res = samplePhys(state, i, max_move + 1, mul, sum, flag, best);
            if(!(res < best))continue;  best = res;  dir = i;
        }
    //cout << "Best dir: " << dir << ", danger: " << best << endl;
    return fref[cur].prev_dir = dir;
}


double DangerField::checkTarget(const Target &tank, double angle, double &best_angle, GunMove &res, double best)
{
    double a = rem(angle - fref[cur].gun_angle - fire_time * fref[cur].ang_spd, 2 * M_PI);
    double left_time = (2 * M_PI - a) / gun_spd_n, right_time = a / gun_spd_p;  int start;
    if(left_time < right_time)
    {
        start = (int)ceil(left_time);  a -= 2 * M_PI;
    }
    else start = (int)ceil(right_time);
    start = max(0, start - fire_time);

    Vec2D dir = sincos(angle);
    ShellRef shell(fref[cur].pos, dir, fref[cur].gun_len, REGULAR);
    double dist = checkRay(shell, quad_index, tank.quad_index);
    int total = (int)min(1e6, ceil(shellFlyTime(dist, REGULAR)));
    double sc = tank.calcScore(shell, start, total);
    FireType fire = REGULAR_FIRE;
    if(fref[cur].premium)
    {
        shell = ShellRef(fref[cur].pos, dir, fref[cur].gun_len, PREMIUM);
        total = (int)min(1e6, ceil(shellFlyTime(dist, PREMIUM)));
        double sc_p = (prm.tg_prem_bonus + 1) * tank.calcScore(shell, start, total) - prm.tg_prem_offs;
        if(sc_p > sc)
        {
            sc = sc_p;  fire = PREMIUM_FIRE;
        }
    }
    if(!(sc > best))return best;

    if(sc < prm.tg_fire_thr && (cur_tick % 64 || cur_tick / 64 % fref.size() != cur))fire = NONE;

    res.fire_type = (!fire_time && abs(a) < 1e-3 ? fire : NONE);
    best_angle = angle;  res.gun_move = a - fref[cur].ang_spd;  return sc;
}


void Target::generate(const Tank &tank)
{
    delta_min = -tank.engine_rear_power_factor();  delta_max = 1;

    double damp = tank_info[tank.type()].damp;
    double rot_damp = tank_info[tank.type()].rot_damp;
    double force = 0.5 + tank.crew_health() / (2.0 * tank.crew_max_health());
    force *= tank_info[tank.type()].force;

    pred.resize(max_pred);  pred[0].pos = Vec2D(tank.x(), tank.y());
    pred[0].delta = Vec2D(0, 0);  pred[0].dir = sincos(tank.angle());
    pred[0].min = delta_min;  pred[0].max = delta_max;

    Vec2D spd(tank.speed_x(), tank.speed_y()), spd_delta(0, 0);
    double angle(tank.angle()), ang_spd(tank.angular_speed());
    for(int i = 1; i < max_pred; i++)
    {
        spd_delta += force * pred[i - 1].dir - damp * spd_delta;
        spd -= damp * spd;  ang_spd -= rot_damp * ang_spd;

        pred[i].pos = pred[i - 1].pos + spd;
        pred[i].delta = pred[i - 1].delta + spd_delta;
        pred[i].dir = sincos(angle += ang_spd);

        double border = half_w / pred[i].delta.len();
        Vec2D inv(1 / pred[i].delta.x, 1 / pred[i].delta.y);
        Vec2D delta = DangerField::size / 2, center = delta - pred[i].pos;
        if(inv.x < 0)delta.x = -delta.x;  if(inv.y < 0)delta.y = -delta.y;
        double cur_min = max(pred[i - 1].min - border, max((center.x - delta.x) * inv.x, (center.y - delta.y) * inv.y));
        double cur_max = min(pred[i - 1].max + border, min((center.x + delta.x) * inv.x, (center.y + delta.y) * inv.y));
        for(size_t j = 0; j < DangerField::block_count; j++)
            if(j != quad_index)
            {
                double t_min, t_max;
                DangerField::quad[j].crossLine(pred[i].pos, pred[i].delta, t_min, t_max);
                if(t_min < cur_min && t_max > cur_min)cur_min = t_max;
                if(t_min < cur_max && t_max > cur_max)cur_max = t_min;
            }
        cur_min += border;  cur_max -= border;
        if(cur_min > cur_max)cur_min = cur_max = (cur_min + cur_max) / 2;
        pred[i].min = cur_min;  pred[i].max = cur_max;
    }
}

void Target::calcRange(ShellRef shell, int step, int total, ScoreRange &range) const
{
    double score = exp(-step / prm.tg_lookahead);
    int end = step + total;  if(end > max_pred)end = max_pred;
    for(; step < end; step++, score *= dmul)
    {
        double t_min, t_max;
        shell.crossRange(Quad(pred[step].pos, pred[step].dir, half_w, half_h), pred[step].delta, t_min, t_max);
        t_min = max(pred[step].min, t_min);  t_max = min(pred[step].max, t_max);
        if(t_min < t_max)
        {
            double score1 = score * sqr(shell.dir * pred[step].dir);
            double score2 = score * sqr(shell.dir % pred[step].dir);

            Vec2D dr = shell.pos - pred[step].pos;
            if(dr % pred[step].delta < 0)swap(score1, score2);
            Vec2D diag1 = half_w * pred[step].dir + half_h * ~pred[step].dir;
            Vec2D diag2 = half_w * pred[step].dir - half_h * ~pred[step].dir;
            double div1 = (dr % diag1) / (pred[step].delta % diag1);
            double div2 = (dr % diag2) / (pred[step].delta % diag2);
            if(div1 > div2)
            {
                swap(div1, div2);  swap(score1, score2);
            }

            int index = 1;
            ScoreElem elem[4] = {ScoreElem(t_min == pred[step].min ? delta_min : t_min, score1)};
            if(div1 > t_min)
            {
                if(div1 < t_max)
                {
                    elem[index++] = ScoreElem(div1, score2);
                    if(div2 < t_max)elem[index++] = ScoreElem(div2, score1);
                }
            }
            else if(div2 > t_min)
            {
                elem[0].val = score2;
                if(div2 < t_max)elem[index++] = ScoreElem(div2, score1);
            }
            elem[index++] = ScoreElem(t_max == pred[step].max ? delta_max : t_max, 0);
            range.merge(elem, index);
        }
        shell.advance();
    }
}


inline void printValues(double up, double dn, int flag)
{
    static const char gradient[] =
        "000 232 233 234 235 236 237 238 239 240 241 242 243 244 245 246 247 248 249 250 251 252 253 254 255 015";

    cout << "\x1B[48;5;";
    if(flag & 1)cout << 10;
    else cout.write(gradient + 4 * min(max(0, int(up * 26)), 25), 3);  cout << ";38;5;";
    if(flag & 2)cout << 10;
    else cout.write(gradient + 4 * min(max(0, int(dn * 26)), 25), 3);  cout << "m▄";
}

void DangerField::print()
{
    static const double offs = 0, scale = 0.5;

    Vec2D index = (fref[cur].pos - offset) / h;
    size_t k0 = size_t(floor(index.x + 0.5)) + size_t(floor(index.y + 0.5)) * width;

    cout << "\x1B[" << height << 'A';
    for(size_t j = 0, k = 0; j < height; j += 2, k += width)
    {
        for(size_t i = 0; i < width; i++, k++)
            printValues((danger[k] + offs) * scale, (danger[k + width] + offs) * scale,
                k == k0 ? 1 : k + width == k0 ? 2 : 0);
        cout << "\x1B[0m" << endl;
    }
}


clock_t global_time;

void MyStrategy::Move(Tank self, World world, model::Move& move)
{
    DangerField field(world, self);
    if(field.cur == size_t(-1))return;

    move.set_fire_type(field.fire_type);
    move.set_turret_turn(field.gun_move);


    static const double moves[][2] =
    {
        {0, 0}, {1, -1}, {-1, 1}, {1, 1}, {-1, -1},
        {1, 0.9}, {0.9, 1}, {-1, -0.9}, {-0.9, -1},
        {1, 0.8}, {0.8, 1}, {-1, -0.8}, {-0.8, -1},
        {1, 0.7}, {0.7, 1}, {-1, -0.7}, {-0.7, -1},
        {1, 0.6}, {0.6, 1}, {-1, -0.6}, {-0.6, -1},
        //{1, 0.5}, {0.5, 1}, {-1, -0.5}, {-0.5, -1},
        {1, 0.4}, {0.4, 1}, {-1, -0.4}, {-0.4, -1},
        //{1, 0.3}, {0.3, 1}, {-1, -0.3}, {-0.3, -1},
        {1, 0.2}, {0.2, 1}, {-1, -0.2}, {-0.2, -1},
        //{1, 0.1}, {0.1, 1}, {-1, -0.1}, {-0.1, -1},
        {1, 0.0}, {0.0, 1}, {-1, -0.0}, {-0.0, -1},
        //{1, -0.1}, {-0.1, 1}, {-1, 0.1}, {0.1, -1},
        {1, -0.2}, {-0.2, 1}, {-1, 0.2}, {0.2, -1},
        //{1, -0.3}, {-0.3, 1}, {-1, 0.3}, {0.3, -1},
        {1, -0.4}, {-0.4, 1}, {-1, 0.4}, {0.4, -1},
        //{1, -0.5}, {-0.5, 1}, {-1, 0.5}, {0.5, -1},
        {1, -0.6}, {-0.6, 1}, {-1, 0.6}, {0.6, -1},
        //{1, -0.7}, {-0.7, 1}, {-1, 0.7}, {0.7, -1},
        {1, -0.8}, {-0.8, 1}, {-1, 0.8}, {0.8, -1},
        //{1, -0.9}, {-0.9, 1}, {-1, 0.9}, {0.9, -1},
    };

    static const size_t max_move[] = {sizeof(moves) / sizeof(moves[0]), 1};

    size_t dir = field.samplePhys(self, moves, max_move);
    move.set_left_track_power(moves[dir][0]);
    move.set_right_track_power(moves[dir][1]);


    /*if(world.tick() % 100 == 99)
    {
        clock_t old = global_time;  global_time = clock();
        cout << "Time per tick: " << (global_time - old) * (10.0 / CLOCKS_PER_SEC) << "ms" << endl;
    }*/
}

TankType MyStrategy::SelectTank(int tank_index, int team_size)
{
    global_time = clock();

    return MEDIUM;
}