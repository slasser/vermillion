import codecs
import json
import random
import sys
random.seed(13)

def choose_n(xs, n):
    return [random.choice(xs) for i in range(n)]    

def make_prizes_dict(prizes):
    return {"prizes" : prizes}

def write_datafile(d, out_dir, sz):
    fname = "{}/nobel_{:05d}.json".format(out_dir, sz)
    with codecs.open(fname, "w", encoding="utf8") as fh:
        json.dump(d, fh, ensure_ascii=False)

def create_datafile(prizes, out_dir, sz):
    dfile_prizes      = choose_n(prizes, sz)
    dfile_prizes_dict = make_prizes_dict(dfile_prizes)
    write_datafile(dfile_prizes_dict, out_dir, sz)

def generate_data(min_sz, max_sz, step, nobel_file, out_dir):
    with open(nobel_file, "r") as fh:
        jdict  = json.load(fh)
        prizes = jdict["prizes"]
        for sz in range(min_sz, max_sz, step):
            create_datafile(prizes, out_dir, sz)
            
if __name__ == "__main__":
    generate_data(int(sys.argv[1]), 
                  int(sys.argv[2]), 
                  int(sys.argv[3]), 
                  "nobel_100yrs.json",
                  "gendata")
