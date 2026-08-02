/* ═══════════════════════════════════════════════════════════
 *  oasm - OS/2026 Self-Hosted x86-32 Assembler
 *  Usage: run oasm input.asm output.elf
 *  Supports: mov,add,sub,and,or,xor,cmp,push,pop,inc,dec,
 *            jmp,je,jne,jl,jg,call,ret,int,nop,hlt,lea,
 *            shl,shr,mul,div,neg,not,test,db,dw,dd,equ
 * ═══════════════════════════════════════════════════════════ */

/* ─── OS/2026 syscall wrappers ─── */
static int sys(int n,int a,int b,int c){
    int r; __asm__ volatile("int $0x80":"=a"(r):"a"(n),"b"(a),"c"(b),"d"(c)); return r;
}
#define S_PUTC(c)    sys(50,(c),0,0)
#define S_PUTS(s)    sys(51,(int)(s),0,0)
#define S_ARGC()     sys(40,0,0,0)
#define S_ARGV(i,b,n) sys(41,(i),(int)(b),(n))
#define S_EXIT()     sys(91,0,0,0)
#define S_FSTAT(n,d) sys(68,(int)(n),(int)(d),0)
#define S_FLOAD(d,b) sys(61,(int)(d),(int)(b),0)
#define S_FWRITE(n,d,s) sys(62,(int)(n),(int)(d),(s))
#define S_UINT(v)    sys(55,(v),0,0)

static int o_strlen(const char*s){int n=0;while(s[n])n++;return n;}
static int o_strcmp(const char*a,const char*b){while(*a&&*a==*b){a++;b++;}return*(unsigned char*)a-*(unsigned char*)b;}
static int o_strncmp(const char*a,const char*b,int n){for(int i=0;i<n;i++){if(a[i]!=b[i])return a[i]-b[i];if(!a[i])return 0;}return 0;}

static void o_print(const char*s){S_PUTS(s);}
static void o_printnum(int v){
    if(v<0){S_PUTC('-');v=-v;}
    char b[12];int n=0;
    if(!v){S_PUTC('0');return;}
    while(v){b[n++]='0'+v%10;v/=10;}
    while(n--)S_PUTC(b[n]);
}

/* ─── 출력 버퍼 ─── */
#define CODE_MAX 32768
static unsigned char code[CODE_MAX];
static int code_len=0;

static void emit8(unsigned char b){if(code_len<CODE_MAX)code[code_len++]=b;}
static void emit16(unsigned short w){emit8(w&0xFF);emit8(w>>8);}
static void emit32(unsigned int d){emit8(d&0xFF);emit8((d>>8)&0xFF);emit8((d>>16)&0xFF);emit8(d>>24);}

/* ─── 라벨/심볼 테이블 ─── */
#define MAX_LABELS 128
#define MAX_FIXUPS 256
typedef struct{char name[32];int addr;int defined;}label_t;
typedef struct{int offset;int label_idx;int rel;int size;}fixup_t;

static label_t labels[MAX_LABELS];
static int nlabels=0;
static fixup_t fixups[MAX_FIXUPS];
static int nfixups=0;

static int find_label(const char*name){
    for(int i=0;i<nlabels;i++) if(!o_strcmp(labels[i].name,name)) return i;
    return -1;
}
static int add_label(const char*name){
    int i=find_label(name);
    if(i>=0) return i;
    if(nlabels>=MAX_LABELS){o_print("too many labels\n");return -1;}
    i=nlabels++;
    for(int j=0;name[j]&&j<31;j++) labels[i].name[j]=name[j];
    labels[i].name[31]=0;
    labels[i].addr=0; labels[i].defined=0;
    return i;
}
static void add_fixup(int label_idx,int offset,int relative,int size){
    if(nfixups>=MAX_FIXUPS){o_print("too many fixups\n");return;}
    fixups[nfixups].offset=offset;
    fixups[nfixups].label_idx=label_idx;
    fixups[nfixups].rel=relative;
    fixups[nfixups].size=size;
    nfixups++;
}

/* ─── 토크나이저 ─── */
#define TOK_MAX 16
static char tokens[TOK_MAX][64];
static int ntokens;

static void skip_ws(const char**p){while(**p==' '||**p=='\t')(*p)++;}

static int is_digit(char c){return c>='0'&&c<='9';}
static int is_alpha(char c){return(c>='a'&&c<='z')||(c>='A'&&c<='Z')||c=='_'||c=='.';}
static int is_alnum(char c){return is_alpha(c)||is_digit(c);}
static char to_lower(char c){return(c>='A'&&c<='Z')?c+32:c;}

static void tokenize(const char*line){
    ntokens=0;
    const char*p=line;
    skip_ws(&p);
    while(*p&&*p!=';'&&*p!='\n'&&*p!='\r'&&ntokens<TOK_MAX){
        int ti=0;
        if(*p==','||*p=='['||*p==']'||*p=='+'||*p=='-'||*p=='*'){
            tokens[ntokens][0]=*p++; tokens[ntokens][1]=0; ntokens++;
        } else if(*p=='"'||*p=='\''){
            char q=*p++;
            while(*p&&*p!=q&&ti<62) tokens[ntokens][ti++]=*p++;
            if(*p==q) p++;
            tokens[ntokens][ti]=0; ntokens++;
        } else if(is_alpha(*p)){
            while(is_alnum(*p)&&ti<62) tokens[ntokens][ti++]=to_lower(*p++);
            tokens[ntokens][ti]=0; ntokens++;
        } else if(is_digit(*p)||(*p=='0'&&(p[1]=='x'||p[1]=='X'))){
            while((is_alnum(*p))&&ti<62) tokens[ntokens][ti++]=*p++;
            tokens[ntokens][ti]=0; ntokens++;
        } else if(*p==':'){
            tokens[ntokens][0]=*p++; tokens[ntokens][1]=0; ntokens++;
        } else p++;
        skip_ws(&p);
    }
}

/* ─── 숫자 파싱 ─── */
static int parse_num(const char*s,int*val){
    int v=0,neg=0;
    if(*s=='-'){neg=1;s++;}
    if(s[0]=='0'&&(s[1]=='x'||s[1]=='X')){
        s+=2;
        if(!((*s>='0'&&*s<='9')||(to_lower(*s)>='a'&&to_lower(*s)<='f'))) return 0;
        while(*s){
            char c=to_lower(*s++);
            if(c>='0'&&c<='9') v=v*16+c-'0';
            else if(c>='a'&&c<='f') v=v*16+c-'a'+10;
            else break;
        }
    } else {
        if(!(*s>='0'&&*s<='9')) return 0;  /* 숫자 아니면 실패 */
        while(*s>='0'&&*s<='9') v=v*10+(*s++)-'0';
    }
    *val=neg?-v:v;
    return 1;
}

/* ─── 레지스터 파싱 ─── */
static const char*reg32_names[]={"eax","ecx","edx","ebx","esp","ebp","esi","edi"};
static const char*reg8_names[]={"al","cl","dl","bl","ah","ch","dh","bh"};

static int parse_reg32(const char*s){
    for(int i=0;i<8;i++) if(!o_strcmp(s,reg32_names[i])) return i;
    return -1;
}
static int parse_reg8(const char*s){
    for(int i=0;i<8;i++) if(!o_strcmp(s,reg8_names[i])) return i;
    return -1;
}

/* ─── ModR/M 인코딩 ─── */
static void emit_modrm(int mod,int reg,int rm){
    emit8((unsigned char)((mod<<6)|(reg<<3)|rm));
}

/* ─── 명령어 어셈블 ─── */
#define BASE_ADDR 0x00800000

/* ALU 연산 공통 (add=0,or=1,adc=2,sbb=3,and=4,sub=5,xor=6,cmp=7) */
static void asm_alu(int op, int t){
    /* t = token index after mnemonic */
    int dst=parse_reg32(tokens[t]);
    if(dst<0){o_print("bad reg\n");return;}
    if(ntokens<=t+2){o_print("missing operand\n");return;}
    /* skip comma */
    int s=t+2;
    int src=parse_reg32(tokens[s]);
    if(src>=0){
        /* reg,reg */
        emit8((unsigned char)(op*8+1)); emit_modrm(3,src,dst);
    } else {
        /* reg,imm */
        int val;
        if(parse_num(tokens[s],&val)){
            if(dst==0){emit8((unsigned char)(op*8+5));emit32(val);} /* AL/EAX short form */
            else{emit8(0x81);emit_modrm(3,op,dst);emit32(val);}
        } else {
            /* reg,label (mov-like, treat as immediate) */
            int li=add_label(tokens[s]);
            emit8(0x81);emit_modrm(3,op,dst);
            add_fixup(li,code_len,0,4);emit32(0);
        }
    }
}

static void asm_line(void){
    if(ntokens==0) return;

    /* label: 체크 */
    int ti=0;
    if(ntokens>=2 && !o_strcmp(tokens[1],":")){
        /* standalone label */
        int li=add_label(tokens[0]);
        labels[li].addr=code_len;
        labels[li].defined=1;
        ti=2;
    } else if(tokens[0][o_strlen(tokens[0])-1]==':'){
        /* label with colon attached */
        char lbl[32];int li2=0;
        while(tokens[0][li2]&&tokens[0][li2]!=':'&&li2<31){lbl[li2]=tokens[0][li2];li2++;}
        lbl[li2]=0;
        int idx=add_label(lbl);
        labels[idx].addr=code_len;
        labels[idx].defined=1;
        ti=1;
    }

    if(ti>=ntokens) return;
    const char*mn=tokens[ti];

    /* 디렉티브 */
    if(!o_strcmp(mn,"db")){
        for(int i=ti+1;i<ntokens;i++){
            if(tokens[i][0]==','||tokens[i][0]=='['||tokens[i][0]==']') continue;
            int v; if(parse_num(tokens[i],&v)) emit8((unsigned char)v);
            else { /* string */ for(int j=0;tokens[i][j];j++) emit8((unsigned char)tokens[i][j]); }
        }
        return;
    }
    if(!o_strcmp(mn,"dw")){
        for(int i=ti+1;i<ntokens;i++){
            if(tokens[i][0]==',') continue;
            int v; parse_num(tokens[i],&v); emit16((unsigned short)v);
        }
        return;
    }
    if(!o_strcmp(mn,"dd")){
        for(int i=ti+1;i<ntokens;i++){
            if(tokens[i][0]==',') continue;
            int v;
            if(parse_num(tokens[i],&v)) emit32((unsigned int)v);
            else { int li=add_label(tokens[i]); add_fixup(li,code_len,0,4); emit32(0); }
        }
        return;
    }
    if(!o_strcmp(mn,"equ")){
        if(ti>0){
            int val; parse_num(tokens[ti+1],&val);
            int li=add_label(tokens[ti-1]);
            labels[li].addr=val; labels[li].defined=1;
        }
        return;
    }
    if(!o_strcmp(mn,"section")||!o_strcmp(mn,"global")||!o_strcmp(mn,"bits")||!o_strcmp(mn,"org")) return;

    /* ── NOP, RET, HLT, CLI, STI ── */
    if(!o_strcmp(mn,"nop")){emit8(0x90);return;}
    if(!o_strcmp(mn,"ret")){emit8(0xC3);return;}
    if(!o_strcmp(mn,"hlt")){emit8(0xF4);return;}
    if(!o_strcmp(mn,"cli")){emit8(0xFA);return;}
    if(!o_strcmp(mn,"sti")){emit8(0xFB);return;}
    if(!o_strcmp(mn,"pusha")){emit8(0x60);return;}
    if(!o_strcmp(mn,"popa")){emit8(0x61);return;}
    if(!o_strcmp(mn,"cdq")){emit8(0x99);return;}
    if(!o_strcmp(mn,"rep")){emit8(0xF3);return;}
    if(!o_strcmp(mn,"movsb")){emit8(0xA4);return;}
    if(!o_strcmp(mn,"stosb")){emit8(0xAA);return;}
    if(!o_strcmp(mn,"movsd")){emit8(0xA5);return;}
    if(!o_strcmp(mn,"stosd")){emit8(0xAB);return;}

    /* ── INT imm8 ── */
    if(!o_strcmp(mn,"int")){
        int v; parse_num(tokens[ti+1],&v);
        emit8(0xCD); emit8((unsigned char)v);
        return;
    }

    /* ── PUSH/POP ── */
    if(!o_strcmp(mn,"push")){
        int r=parse_reg32(tokens[ti+1]);
        if(r>=0){emit8((unsigned char)(0x50+r));}
        else{int v;parse_num(tokens[ti+1],&v);emit8(0x68);emit32(v);}
        return;
    }
    if(!o_strcmp(mn,"pop")){
        int r=parse_reg32(tokens[ti+1]);
        if(r>=0) emit8((unsigned char)(0x58+r));
        return;
    }

    /* ── INC/DEC ── */
    if(!o_strcmp(mn,"inc")){int r=parse_reg32(tokens[ti+1]);if(r>=0)emit8((unsigned char)(0x40+r));return;}
    if(!o_strcmp(mn,"dec")){int r=parse_reg32(tokens[ti+1]);if(r>=0)emit8((unsigned char)(0x48+r));return;}

    /* ── NEG/NOT ── */
    if(!o_strcmp(mn,"neg")){int r=parse_reg32(tokens[ti+1]);if(r>=0){emit8(0xF7);emit_modrm(3,3,r);}return;}
    if(!o_strcmp(mn,"not")){int r=parse_reg32(tokens[ti+1]);if(r>=0){emit8(0xF7);emit_modrm(3,2,r);}return;}

    /* ── MUL/DIV (unsigned, eax *= r) ── */
    if(!o_strcmp(mn,"mul")){int r=parse_reg32(tokens[ti+1]);if(r>=0){emit8(0xF7);emit_modrm(3,4,r);}return;}
    if(!o_strcmp(mn,"div")){int r=parse_reg32(tokens[ti+1]);if(r>=0){emit8(0xF7);emit_modrm(3,6,r);}return;}
    if(!o_strcmp(mn,"imul")){int r=parse_reg32(tokens[ti+1]);if(r>=0){emit8(0xF7);emit_modrm(3,5,r);}return;}
    if(!o_strcmp(mn,"idiv")){int r=parse_reg32(tokens[ti+1]);if(r>=0){emit8(0xF7);emit_modrm(3,7,r);}return;}

    /* ── SHL/SHR ── */
    if(!o_strcmp(mn,"shl")){
        int r=parse_reg32(tokens[ti+1]);
        if(r>=0&&ntokens>ti+3){
            int v; parse_num(tokens[ti+3],&v);
            if(v==1){emit8(0xD1);emit_modrm(3,4,r);}
            else{emit8(0xC1);emit_modrm(3,4,r);emit8((unsigned char)v);}
        }return;
    }
    if(!o_strcmp(mn,"shr")){
        int r=parse_reg32(tokens[ti+1]);
        if(r>=0&&ntokens>ti+3){
            int v; parse_num(tokens[ti+3],&v);
            if(v==1){emit8(0xD1);emit_modrm(3,5,r);}
            else{emit8(0xC1);emit_modrm(3,5,r);emit8((unsigned char)v);}
        }return;
    }

    /* ── ALU: add,sub,and,or,xor,cmp,test ── */
    if(!o_strcmp(mn,"add")){asm_alu(0,ti+1);return;}
    if(!o_strcmp(mn,"or")) {asm_alu(1,ti+1);return;}
    if(!o_strcmp(mn,"and")){asm_alu(4,ti+1);return;}
    if(!o_strcmp(mn,"sub")){asm_alu(5,ti+1);return;}
    if(!o_strcmp(mn,"xor")){asm_alu(6,ti+1);return;}
    if(!o_strcmp(mn,"cmp")){asm_alu(7,ti+1);return;}
    if(!o_strcmp(mn,"test")){
        int r1=parse_reg32(tokens[ti+1]),r2=parse_reg32(tokens[ti+3]);
        if(r1>=0&&r2>=0){emit8(0x85);emit_modrm(3,r2,r1);}
        return;
    }

    /* ── MOV ── */
    if(!o_strcmp(mn,"mov")){
        int dst=parse_reg32(tokens[ti+1]);
        if(dst>=0 && ntokens>ti+3){
            int src=parse_reg32(tokens[ti+3]);
            if(src>=0){
                /* mov reg,reg */
                emit8(0x89); emit_modrm(3,src,dst);
            } else if(tokens[ti+3][0]=='['){
                /* mov reg,[mem] */
                int base_r=-1,disp=0;
                if(ntokens>ti+4) base_r=parse_reg32(tokens[ti+4]);
                if(base_r>=0){
                    if(ntokens>ti+6){parse_num(tokens[ti+6],&disp);emit8(0x8B);if(disp){emit_modrm(2,dst,base_r);emit32(disp);}else{emit_modrm(0,dst,base_r);}}
                    else{emit8(0x8B);emit_modrm(0,dst,base_r);}
                } else {
                    /* mov reg,[addr] */
                    int addr; parse_num(tokens[ti+4],&addr);
                    emit8(0x8B);emit_modrm(0,dst,5);emit32(addr);
                }
            } else {
                /* mov reg,imm/label */
                int val;
                if(parse_num(tokens[ti+3],&val)){
                    emit8((unsigned char)(0xB8+dst)); emit32(val);
                } else {
                    int li=add_label(tokens[ti+3]);
                    emit8((unsigned char)(0xB8+dst));
                    add_fixup(li,code_len,0,4); emit32(0);
                }
            }
        } else if(tokens[ti+1][0]=='[' && ntokens>ti+4){
            /* mov [mem],reg/imm */
            int base_r=parse_reg32(tokens[ti+2]);
            /* skip until comma then find source */
            int si=ti+1;
            while(si<ntokens && o_strcmp(tokens[si],",")) si++;
            si++;
            if(si<ntokens){
                int src=parse_reg32(tokens[si]);
                if(src>=0 && base_r>=0){
                    int disp=0;
                    if(ntokens>ti+4 && !o_strcmp(tokens[ti+3],"+")){parse_num(tokens[ti+4],&disp);emit8(0x89);emit_modrm(2,src,base_r);emit32(disp);}
                    else{emit8(0x89);emit_modrm(0,src,base_r);}
                } else if(base_r>=0){
                    /* mov [reg],imm */
                    int val;parse_num(tokens[si],&val);
                    emit8(0xC7);emit_modrm(0,0,base_r);emit32(val);
                }
            }
        }
        return;
    }

    /* ── LEA ── */
    if(!o_strcmp(mn,"lea")){
        int dst=parse_reg32(tokens[ti+1]);
        if(dst>=0 && ntokens>ti+4 && tokens[ti+3][0]=='['){
            int base_r=parse_reg32(tokens[ti+4]);
            if(base_r>=0 && ntokens>ti+6){
                int disp; parse_num(tokens[ti+6],&disp);
                emit8(0x8D);emit_modrm(2,dst,base_r);emit32(disp);
            }
        }
        return;
    }

    /* ── XCHG ── */
    if(!o_strcmp(mn,"xchg")){
        int r1=parse_reg32(tokens[ti+1]),r2=parse_reg32(tokens[ti+3]);
        if(r1>=0&&r2>=0){
            if(r1==0){emit8((unsigned char)(0x90+r2));}
            else if(r2==0){emit8((unsigned char)(0x90+r1));}
            else{emit8(0x87);emit_modrm(3,r1,r2);}
        }
        return;
    }

    /* ── JMP/CALL ── */
    if(!o_strcmp(mn,"jmp")){
        int r=parse_reg32(tokens[ti+1]);
        if(r>=0){emit8(0xFF);emit_modrm(3,4,r);} /* jmp reg */
        else{int li=add_label(tokens[ti+1]);emit8(0xE9);add_fixup(li,code_len,1,4);emit32(0);}
        return;
    }
    if(!o_strcmp(mn,"call")){
        int r=parse_reg32(tokens[ti+1]);
        if(r>=0){emit8(0xFF);emit_modrm(3,2,r);}
        else{int li=add_label(tokens[ti+1]);emit8(0xE8);add_fixup(li,code_len,1,4);emit32(0);}
        return;
    }

    /* ── Jcc (conditional jumps) ── */
    static const char*jcc_names[]={"jo","jno","jb","jnb","je","jne","jbe","ja",
                                    "js","jns","jp","jnp","jl","jge","jle","jg",
                                    "jz","jnz","jc","jnc","jae","jna",0};
    static const int jcc_codes[]={0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,
                                   4,5,2,3,3,6};
    for(int i=0;jcc_names[i];i++){
        if(!o_strcmp(mn,jcc_names[i])){
            int li=add_label(tokens[ti+1]);
            emit8(0x0F);emit8((unsigned char)(0x80+jcc_codes[i]));
            add_fixup(li,code_len,1,4);emit32(0);
            return;
        }
    }

    /* ── SYSCALL shorthand: syscall N → mov eax,N; int 0x80 ── */
    if(!o_strcmp(mn,"syscall")){
        if(ntokens>ti+1){int v;parse_num(tokens[ti+1],&v);emit8(0xB8);emit32(v);}
        emit8(0xCD);emit8(0x80);
        return;
    }

    o_print("? "); o_print(mn); o_print("\n");
}

/* ─── ELF32 생성 ─── */
static unsigned char elf_out[CODE_MAX+256];
static int elf_len=0;

static void elf_write8(unsigned char b){elf_out[elf_len++]=b;}
static void elf_write32(unsigned int v){
    elf_out[elf_len++]=v&0xFF;elf_out[elf_len++]=(v>>8)&0xFF;
    elf_out[elf_len++]=(v>>16)&0xFF;elf_out[elf_len++]=v>>24;
}
static void elf_write16(unsigned short v){elf_out[elf_len++]=v&0xFF;elf_out[elf_len++]=v>>8;}

static int build_elf(void){
    unsigned int entry = BASE_ADDR;
    unsigned int code_offset = 0x54; /* ELF header(52) + 1 phdr(32) = 84 = 0x54 */
    unsigned int load_addr = BASE_ADDR;

    elf_len=0;
    /* ELF header */
    elf_write8(0x7F);elf_write8('E');elf_write8('L');elf_write8('F'); /* magic */
    elf_write8(1);elf_write8(1);elf_write8(1);elf_write8(0); /* 32bit,LE,v1,SYSV */
    for(int i=0;i<8;i++) elf_write8(0); /* padding */
    elf_write16(2); /* ET_EXEC */
    elf_write16(3); /* EM_386 */
    elf_write32(1); /* EV_CURRENT */
    elf_write32(entry); /* e_entry */
    elf_write32(0x34); /* e_phoff = 52 */
    elf_write32(0); /* e_shoff */
    elf_write32(0); /* e_flags */
    elf_write16(52); /* e_ehsize */
    elf_write16(32); /* e_phentsize */
    elf_write16(1); /* e_phnum */
    elf_write16(0); /* e_shentsize */
    elf_write16(0); /* e_shnum */
    elf_write16(0); /* e_shstrndx */

    /* Program header (PT_LOAD) */
    elf_write32(1); /* PT_LOAD */
    elf_write32(code_offset); /* p_offset */
    elf_write32(load_addr); /* p_vaddr */
    elf_write32(load_addr); /* p_paddr */
    elf_write32(code_len); /* p_filesz */
    elf_write32(code_len+4096); /* p_memsz (extra for BSS) */
    elf_write32(7); /* PF_R|PF_W|PF_X */
    elf_write32(0x1000); /* p_align */

    /* Code */
    for(int i=0;i<code_len;i++) elf_write8(code[i]);

    return elf_len;
}

/* ─── 메인 ─── */
static char src_buf[32768];

void _start(void){
    o_print("oasm v1.0 - OS/2026 Assembler\n");

    int argc=S_ARGC();
    char infile[64]={0}, outfile[64]={0};
    if(argc>=2) S_ARGV(1,infile,63);
    if(argc>=3) S_ARGV(2,outfile,63);
    else{
        /* default output name */
        for(int i=0;infile[i]&&i<58;i++) outfile[i]=infile[i];
        /* replace .asm with .elf */
        int l=o_strlen(outfile);
        if(l>4&&outfile[l-4]=='.'){outfile[l-3]='e';outfile[l-2]='l';outfile[l-1]='f';}
        else{outfile[l]='.';outfile[l+1]='e';outfile[l+2]='l';outfile[l+3]='f';outfile[l+4]=0;}
    }
    if(!infile[0]){o_print("Usage: run oasm input.asm [output.elf]\n");S_EXIT();return;}

    o_print("Input: "); o_print(infile); o_print("\n");
    o_print("Output: "); o_print(outfile); o_print("\n");

    /* 파일 로드 */
    typedef struct{char name[24];unsigned int lba;unsigned int size;}de_t;
    de_t de;
    if(!S_FSTAT(infile,&de)){o_print("File not found\n");S_EXIT();return;}
    if(de.size>32000){o_print("File too large\n");S_EXIT();return;}
    S_FLOAD(&de,src_buf);
    src_buf[de.size]=0;

    o_print("Assembling "); o_printnum(de.size); o_print(" bytes...\n");

    /* 어셈블 */
    code_len=0; nlabels=0; nfixups=0;
    char line[256];
    const char*p=src_buf;
    int lineno=0;
    while(*p){
        int li2=0;
        while(*p&&*p!='\n'&&*p!='\r'&&li2<254) line[li2++]=*p++;
        line[li2]=0;
        if(*p=='\r') p++;
        if(*p=='\n') p++;
        lineno++;

        tokenize(line);
        asm_line();
    }

    /* Fixup 해결 */
    int errors=0;
    for(int i=0;i<nfixups;i++){
        fixup_t*f=&fixups[i];
        if(!labels[f->label_idx].defined){
            o_print("Undefined: "); o_print(labels[f->label_idx].name); o_print("\n");
            errors++;
            continue;
        }
        unsigned int target=labels[f->label_idx].addr + BASE_ADDR;
        if(f->rel){
            /* relative: target - (fixup_addr + 4) */
            int rel_val=(int)target - (int)(f->offset + 4 + BASE_ADDR);
            code[f->offset]=(unsigned char)rel_val;
            code[f->offset+1]=(unsigned char)(rel_val>>8);
            code[f->offset+2]=(unsigned char)(rel_val>>16);
            code[f->offset+3]=(unsigned char)(rel_val>>24);
        } else {
            code[f->offset]=(unsigned char)target;
            code[f->offset+1]=(unsigned char)(target>>8);
            code[f->offset+2]=(unsigned char)(target>>16);
            code[f->offset+3]=(unsigned char)(target>>24);
        }
    }

    if(errors){o_print("Errors found, aborting\n");S_EXIT();return;}

    /* ELF 생성 */
    int elf_size=build_elf();
    o_print("Code: "); o_printnum(code_len); o_print(" bytes\n");
    o_print("ELF:  "); o_printnum(elf_size); o_print(" bytes\n");
    o_print("Labels: "); o_printnum(nlabels); o_print("\n");

    /* 디스크에 저장 */
    S_FWRITE(outfile, elf_out, elf_size);
    o_print("Saved: "); o_print(outfile); o_print("\n");

    S_EXIT();
}
