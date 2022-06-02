"""
@Author : 转接
@Data : 2022/5/23
"""

from typing import Iterable
from prettytable import PrettyTable
from graphviz import Digraph, ExecutableNotFound, CalledProcessError


class Disjoint:  # 并查集, 用于计算等价关系

    def __init__(self, elems={}):
        self.parent = dict()
        for elem in set(elems):
            self.parent[elem] = elem

    def add(self, elem):
        self.parent[elem] = elem

    def root(self, elem):  # 查找某个元素的 root (路径压缩)
        while self.parent[elem] != self.parent[self.parent[elem]]:
            self.parent[elem] = self.parent[self.parent[elem]]
        return self.parent[elem]

    def join(self, elem1, elem2):  # 将两个元素合并
        root1 = self.root(elem1)
        root2 = self.root(elem2)
        self.parent[root1] = root2

    def issame(self, elem1, elem2):  # 判断两个元素是否在同一个集合
        return self.root(elem1) == self.root(elem2)

    def ofroot(self, elem):  # 查询具有公共的某个 root 的所有元素
        return set(filter(lambda e: self.root(e) == elem, self.parent.keys()))

    def allroots(self):  # 查询该并查集内所有作为 root 的元素
        return set(map(lambda e: self.root(e), self.parent.keys()))

    def reset(self, elem):  # 重置某个元素的 parent
        self.parent[elem] = elem


class Automata:
    """
    有穷自动机：
    - 有穷状态集(对应有向图中的节点)
    - 输入字母表(状态转移边的标注)
    - 状态转移规则(对应有向图中的边)
    - 初始状态
    - 终止状态集
    """

    def __init__(self, start, finish, trans):
        """
        params:
        - start: 初始状态, 可为整数或字符串
        - finish: 终止状态集, 可以为列表、元组等
        - trans: 转移规则, 由若干个三元组构成，每个三元组格式为：(src, dst, by) 表示从 src 输入 by 可以转移到 dst, 其中 by 为字母.
        """
        self.states = set()
        self.tokens = set()
        self.finish = set(finish)
        self.trans = dict()
        self.start = start
        for tran in trans:
            src = tran[0]
            dst = tran[1]
            by = tran[2]
            self.states.add(src)  # 原始状态
            self.states.add(dst)  # 目标状态
            if by:
                self.tokens.add(by)  # 转移字母, 用 '' 表示 epsilon
            """
            检查转移图的合法性:
            1. 起始状态必须在状态集中
            2. 终止状态必须在状态集中
            """
            if not src in self.trans.keys():
                self.trans[src] = dict()
            if not by in self.trans[src].keys():
                self.trans[src][by] = set()
            self.trans[src][by].add(dst)  # 创建转移边

        assert start in self.states
        assert isinstance(finish, Iterable)
        assert all(map(lambda x: x in self.states, self.finish))

    def show(self, name):  # 使用 Graphviz 库打印该自动机
        graph = Digraph(name)
        for state in self.states:
            if state in self.finish:
                graph.node(name=str(state), color='black', shape='doublecircle')
            else:
                graph.node(name=str(state), color='black', shape='circle')
            if state == self.start:
                graph.node(name='start', shape='plain')
                graph.edge(tail_name='start', head_name=str(state))
        for src in self.trans.keys():
            for by in self.trans[src].keys():
                for dst in self.trans[src][by]:
                    graph.edge(tail_name=str(src), head_name=str(dst), label=str(by))
        print("尝试打开pdf文件......")
        try:
            graph.view()
        except ExecutableNotFound:
            print("未将graphviz添加到系统环境变量！无法创建并打开pdf文件！")
        except Exception as e:
            print("打开pdf文件失败:"+str(e))

    def print_trans_table(self):  # 打印该自动机的转移矩阵
        tokens = sorted(self.tokens)
        deterministic = self.is_deterministic()
        field_names = tokens if deterministic else (tokens + [''])
        pretty = PrettyTable(field_names=['.'] + field_names)
        for src in self.trans.keys():
            row = [src]
            for token in tokens:
                if not token in self.trans[src].keys():
                    row.append('')
                    continue
                dst = self.trans[src][token]
                if len(dst) > 1:
                    dst = str(dst)
                else:
                    dst = list(dst)[0]
                row.append(dst)
            if not deterministic:  # 非确定
                dst = set()
                for by in self.trans[src]:
                    if not by:
                        dst = dst.union(self.trans[src][by])
                if len(dst) > 1:
                    dst = str(dst)
                elif len(dst) == 1:
                    dst = list(dst)[0]
                else:
                    dst = ''
                row.append(dst)
            pretty.add_row(row)
        print(pretty)

    def is_deterministic(self) -> bool:  # 是否为确定的有穷自动机(DFA)
        """
        检验标准:
        1. 不能有 epsilon 作为输入的字母
        2. 存在某状态对于某字母有多种后继状态
        """
        for state in self.trans.keys():
            for by in self.trans[state].keys():
                if not by:
                    return False
                if len(self.trans[state][by]) > 1:
                    return False
        return True

    def solve_epsilon_closure(self, state):
        assert state in self.states
        closure = set({state})
        while True:
            done = True
            for cstate in closure:
                if not cstate in self.trans.keys():
                    return closure
                for by in self.trans[cstate].keys():
                    if not by:
                        if len(self.trans[cstate][by].difference(closure)) > 0:
                            done = False
                        closure = closure.union(self.trans[cstate][by])
            if done:
                break
        return closure

    def to_deterministic(self):  # 非确定有穷自动机 (NFA) 的确定化, 返回转化后的 DFA, 并输出转化过程的表格
        """
        1. epsilon-闭包，eps-closure(I)，其中 I 为状态集合
        2. I(a) = closure(J), 其中 J 为 I 中每个状态出发经过标记为 a 的弧所到达的集合
        """
        tokens = sorted(self.tokens)  # 按字母的顺序列状态转移
        log_table = []  # 记录画表格的过程
        # 进行 BFS
        queue = []
        visit_list = []
        I_start = self.solve_epsilon_closure(self.start)
        queue.append(I_start)
        visit_list.append(I_start)
        while len(queue) > 0:
            I_now = queue.pop(0)
            # 求 J 与 closure(J)
            row = [I_now]
            for token in tokens:
                J_next = set()
                # 对 I 中的任一个状态，令其先经过 token 再经过 epsilon
                for state in I_now:
                    if (not state in self.trans.keys()) or (not token in self.trans[state].keys()):
                        continue
                    dsts = self.trans[state][token]
                    for dst in dsts:
                        J_next = J_next.union(self.solve_epsilon_closure(dst))
                row.append(J_next)  # 记录 I_a
                if len(J_next) == 0 or J_next in visit_list:
                    continue
                visit_list.append(J_next)
                queue.append(J_next)  # 将新状态插入队列
            log_table.append(row)
        # 输出过程的表格
        pretty = PrettyTable(field_names=[''] + tokens)
        for log in log_table:
            pretty.add_row(list(map(lambda s: 'null' if len(s) == 0 else str(s), log)))
        print(pretty)
        # 构造新的自动机
        nstates = dict()  # 新的状态命名
        for i, nstate in enumerate(visit_list):
            print(f"rename {nstate} --> {i}")  # 可以在这里调整新状态的命名，从 0 开始/从 1 开始/从 'a' 开始 ......
            nstates[str(nstate)] = i
        nstart = nstates[str(I_start)]
        nfinish = set()
        for nstate in visit_list:
            if len(self.finish.intersection(nstate)) > 0:
                nfinish.add(nstates[str(nstate)])
        ntrans = list()
        for log in log_table:
            for i in range(len(tokens)):
                if len(log[i + 1]) > 0:
                    ntrans.append([nstates[str(log[0])], nstates[str(log[i + 1])], tokens[i]])
        # print(ntrans)
        return Automata(nstart, nfinish, ntrans)

    def minify(self):  # 有穷自动机的最小化
        assert self.is_deterministic()  # 必须是确定的有穷自动机
        # 首先用一个并查集表示分区，root 相同的状态位于一个分区
        group_div = Disjoint()
        for state in self.states:
            group_div.add(state)
        # 首先按终止状态和非终止状态分区
        fin = list(self.finish)[0]  # 任取一个终止状态
        for fstate in self.finish:
            group_div.join(fstate, fin)
        if len(self.finish) != len(self.states):  # 有非终止状态, 则初始分成两个区, 否则只有一个初始分区
            nfin = list(self.states.difference(self.finish))[0]  # 任取一个非终止状态
            for state in self.states:
                if not state in self.finish:
                    group_div.join(state, nfin)
        round_count = 0
        while True:
            # 对每个区进行处理, 直到每个区内的状态均两两等价
            groups = group_div.allroots()
            # 输出分区状态
            round_count += 1
            print(f"Minify round {round_count} ......")
            for state in self.states:
                print(f"state {state} is in group {group_div.root(state)}")
            done = True
            for group in groups:  # 对每个区进行处理
                states = list(group_div.ofroot(group))
                equals = Disjoint(states)  # 描述等价关系的并查集
                for i in range(len(states)):
                    for j in range(i + 1, len(states)):
                        state1 = states[i]
                        state2 = states[j]
                        if state1 == state2:
                            continue
                        # 对当前分区的任意两个状态, 每个状态的所有转移都必须到等价的状态
                        # 因为有些状态没有对应输入的转移边，所以：要么都不转移，要么都转移到等价状态 => 等价
                        eq = True
                        for token in self.tokens:
                            can1 = state1 in self.trans.keys() and token in self.trans[state1].keys()
                            can2 = state2 in self.trans.keys() and token in self.trans[state2].keys()
                            if not can1 and not can2:
                                continue
                            if can1 and can2:
                                dst1 = list(self.trans[state1][token])[0]
                                dst2 = list(self.trans[state2][token])[0]
                                adst1 = group_div.root(dst1)
                                adst2 = group_div.root(dst2)
                                if adst1 != adst2:
                                    eq = False
                                    break
                            else:
                                eq = False
                                break
                        if eq:
                            equals.join(state1, state2)
                if len(equals.allroots()) > 1:
                    done = False
                # 对当前区重新分区
                for state in states:
                    group_div.reset(state)
                for state in states:
                    group_div.join(state, equals.root(state))
            if done:
                break
        # 按分区的种类重新编号
        nstate = dict()
        groups = group_div.allroots()
        for i, group in enumerate(groups):
            nstate[group] = i + 1
        # 更新状态转移
        ntrans = []
        for src in self.trans.keys():
            for by in self.trans[src].keys():
                dst = list(self.trans[src][by])[0]
                asrc = nstate[group_div.root(src)]
                adst = nstate[group_div.root(dst)]
                if not [asrc, adst, by] in ntrans:
                    ntrans.append([asrc, adst, by])
        nstart = nstate[group_div.root(self.start)]
        nfinish = set()
        for fstate in self.finish:
            nfinish.add(nstate[group_div.root(fstate)])
        return Automata(nstart, nfinish, ntrans)


state_count = 0
buffer: list = []


def _simp_regex():  # 仅包含基本字符的正则表达式
    global state_count
    global buffer
    state_count += 1
    start = state_count
    last_state = start
    trans = []
    while len(buffer) > 0:
        if buffer[0] != '*' and buffer[0] != '(' and buffer[0] != ')' and buffer[0] != '|':
            if len(buffer) > 1 and buffer[1] == '*':
                state_count += 1
                trans.append([last_state, state_count, ''])
                trans.append([state_count, state_count, buffer[0]])
                trans.append([state_count, state_count + 1, ''])
                state_count += 1
                last_state = state_count
                buffer.pop(0)
                buffer.pop(0)
            else:
                state_count += 1
                trans.append([last_state, state_count, buffer[0]])
                last_state = state_count
                buffer.pop(0)
        else:
            break
    finish_states = (last_state,)
    return start, finish_states, trans


def _sub_regex():
    global buffer
    global state_count
    assert len(buffer) > 0 and buffer[0] == '('
    buffer.pop(0)
    start, finish_states, trans = _regex()
    assert len(buffer) > 0 and buffer[0] == ')'
    buffer.pop(0)
    if len(buffer) > 0 and buffer[0] == '*':
        buffer.pop(0)
        state_count += 1
        nstart = state_count
        state_count += 1
        nfinish = (state_count,)
        trans.append([nstart, start, ''])
        trans.append([nstart, nfinish[0], ''])
        for fstate in finish_states:
            trans.append([fstate, start, ''])
            trans.append([fstate, nfinish[0], ''])
        return nstart, nfinish, trans
    else:
        return start, finish_states, trans


def _concat_nfa(nfa1, nfa2):
    if nfa1 is None:
        return nfa2
    global state_count
    state_count += 1
    start = state_count
    state_count += 1
    finish = (state_count,)
    trans = nfa1[2] + nfa2[2]
    trans.append([start, nfa1[0], ''])
    for fstate in nfa1[1]:
        trans.append([fstate, nfa2[0], ''])
    for fstate in nfa2[1]:
        trans.append([fstate, finish[0], ''])
    return start, finish, trans


def _regex():
    global state_count
    global buffer
    nfa_or = []
    state_count += 1
    start = state_count
    last_nfa = None
    while len(buffer) > 0:
        if buffer[0] == '|':
            nfa_or.append(last_nfa)
            buffer.pop(0)
            last_nfa = None
        elif buffer[0] == '(':
            last_nfa = _concat_nfa(last_nfa, _sub_regex())
        elif buffer[0] == ')':
            break
        else:
            last_nfa = _concat_nfa(last_nfa, _simp_regex())
    nfa_or.append(last_nfa)
    state_count += 1
    finish = (state_count,)
    trans = []
    for nfa in nfa_or:
        trans.append([start, nfa[0], ''])
        trans.extend(nfa[2])
        for fstate in nfa[1]:
            trans.append([fstate, finish[0], ''])
    print(start, finish, trans)
    return start, finish, trans


def regexToAutomata(s: str):  # 将正则表达式翻译为自动机
    global buffer
    global state_count
    state_count = 0
    buffer = list(s)
    start_state, finish_states, trans = _regex()
    return Automata(start=start_state, finish=finish_states, trans=trans)


# 1(1010*|1(010)*1)*0
# D:\Program_Files\Graphviz\bin
try:
    nfa = regexToAutomata(input("输入正则表达式："))
    # nfa = regexToAutomata(r'(a|b)*a(ab)*(a|b)')
    # 输出 NFA
    nfa.print_trans_table()
    nfa.show('NFA')
    dfa = nfa.to_deterministic()  # NFA to DFA
    # 输出 DFA
    dfa.print_trans_table()
    dfa.show('DFA')
    min_dfa = dfa.minify()  # 最小化 DFA
    # 输出最简 DFA
    min_dfa.print_trans_table()
    min_dfa.show('最简DFA')
except TypeError or AssertionError:
    print("输入出错！")
except Exception as e:
    print(repr(e))
