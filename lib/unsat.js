const r=[[10,"+","0"],[3,"+","1"],[1,"+","1"],[7,"+","0"],[4,"+","1"],[3,"-","1"],[8,"+","0"]],sat=a=>{let e=[];return a[r[0][0]]&&"X5"===a[r[0][0]].name&&r.forEach(r=>e.push(`${r[1]}${a[r[0]].name}=${r[2]}`)),e};