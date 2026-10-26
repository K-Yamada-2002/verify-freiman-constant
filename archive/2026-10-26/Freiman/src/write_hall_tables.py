"""Readable tables for the fixed, successfully replayed Hall-ray certificate."""
from layout import DOC
import hashlib
import json
from exact_cf import K
from endpoint_return import BASE


def main():
    source=BASE/'hall_ray_certificate.json'
    data=json.loads(source.read_text())
    checked=json.loads((BASE/'hall_ray_verified.json').read_text())
    assert checked['passed']
    assert hashlib.sha256(source.read_bytes()).hexdigest()==checked['sha256'][source.name]
    lines=['# 半直線証明の初期被覆表','',
           '`hall_ray_certificate.json` の固定リストを表示したもの。',
           '小数は表示用であり、全ての端点・接続の判定は二次体で行う。',
           '型を支える基本帯と一般族の状態番号は JSON に全て保存している。',
           '証明の説明は [HALL_RAY_PROOF.md](HALL_RAY_PROOF.md)。','',
           '## 端点から13/2まで','',
           '入口は中心4、`32113 | 4322` の帯 `[0,1/8]`。左端は厳密に $c_F$。',
           '以下を順に接続する。左端は非中心値上界 $\\Theta$ で切り詰め済み。','',
           '| # | 中心 | 左語 | 右語 | p | q | Θ | 左端 | 右端 |',
           '|---:|---:|---|---|---:|---:|---:|---:|---:|']
    for i,row in enumerate(data['finite_chain'],1):
        lo,hi=(float(K(*x)) for x in row['covered_interval'])
        theta=float(K(*row['theta_upper']))
        lines.append(f"| {i} | {row['center']} | {row['a']} | {row['b']} | {row['band'][0]} | {row['band'][1]} | {theta:.15f} | {lo:.15f} | {hi:.15f} |")
    lines+=['','## 整数移動に用いる [1/2,3/2] の被覆','',
            'この表は中心数字を含まない連分数の和。中心を整数 $n\\ge6$ とすれば、',
            '全ての非中心局所値は6未満となり、平行移動した帯の全点が Markov 値になる。','',
            '| # | 左語 | 右語 | p | q | 左端 | 右端 |',
            '|---:|---|---|---:|---:|---:|---:|']
    for i,row in enumerate(data['translation_chain'],1):
        lo,hi=(float(K(*x)) for x in row['covered_interval'])
        lines.append(f"| {i} | {row['a']} | {row['b']} | {row['band'][0]} | {row['band'][1]} | {lo:.15f} | {hi:.15f} |")
    (DOC/'HALL_RAY_INITIAL_COVER.md').write_text('\n'.join(lines)+'\n')


if __name__=='__main__':main()
