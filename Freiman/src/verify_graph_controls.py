"""Positive closed-family control and gap/endpoint corruption controls."""
from layout import BIN
import json,subprocess
from pathlib import Path
from layout import DATA

BASE=DATA;D=1<<48

def main():
    controls=[]
    for name,pairs,expected in [
        ('cover',[(1,1),(1,2),(2,1),(2,2)],True),
        ('gap',[(1,1),(2,2)],False),
        ('missing_endpoint',[(1,1)],False),
    ]:
        rows=[f'FREIMAN_DYADIC_GRAPH_V1 1 3 0 0 1 {len(pairs)} 0',f'0 {D}']
        rows.extend(f'{u} {w} 0' for u,w in pairs)
        rows.extend([f'{7*D//8} {7*D//8}',f'{9*D//8} {9*D//8}',f'{D} {D}',
                     '0 0 0 0 4',f'0 0',f'{D} {D}',f'{3*D//8} {3*D//8}',f'{5*D//8} {5*D//8}'])
        rows.extend([f'0 0 1 {D} {D} 0 0 {D} {D} 0 1',
                     f'0 0 2 {3*D//8} {3*D//8} 0 0 {3*D//8} {3*D//8} 0 2',
                     f'0 0 2 {3*D//8} {3*D//8} {5*D//8} {5*D//8} {D} {D} 3 1'])
        stem='graph_control_'+name;(BASE/(stem+'.dat')).write_text('\n'.join(rows)+'\n')
        subprocess.run([str(BIN/'graph_kernel'),str(BASE/(stem+'.dat')),str(BASE/(stem+'.json'))],check=True,capture_output=True)
        result=json.loads((BASE/(stem+'.json')).read_text());assert result['closed_family_found']==expected
        controls.append({'name':name,'expected':expected,'actual':result['closed_family_found']})
    result={'passed':True,'controls':controls}
    (BASE/'graph_controls.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
