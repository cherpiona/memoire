
"""
Created on Mon Aug  8 05:34:03 2022

@author: moi
"""
import json
import hashlib
import canonicaljson
import elgamal
import numpy as np
from secrets import randbelow,choice
import random
from timeit import default_timer as timer

"""
fonctions utile
"""
def _hashg(json_obj, q):
    """Hash a JSON object to a integer modulo q.

    :param json_obj: JSON object encoded into a str.

    Procedure:
    * map the object to json in binary canonical form (see
    <https://pypi.org/project/canonicaljson/>)
    * hash it with SHA256
    * interpret the byte string as a big-endian integer
    * reduce it mod q
    """
    return int.from_bytes(
            hashlib.sha256(canonicaljson.dumps(json.loads(json_obj))).digest(),
            byteorder='big'
            ) % q
def inverse(x, p):
    """
    @returns x^-1 in Z*_p
    """
    res = pow(x, p-2, p)
    assert (res * x) % p == 1
    return res

"""
Phase préelection
"""

def generate_empty_bb(p, g):
    return {"group": {"p": p, "g": g}}
"""generation des clefs curateurs"""
def create_clef_curateur_with_proof(bb):
    """
    crée un paire de clef elgamal et la zkp de la connaissance de la 
    clef secrete et poste sur le tableau des bulletins l'ensemble
    """
    group=elgamal.ElgamalGroup(bb["group"]["p"],bb["group"]["g"])
    #crée la paire
    sk,pk=elgamal.gen_elgamal_keypair(group)
    #crée la preuve
    commit_sk,commit_pk = elgamal.gen_elgamal_keypair(group)
    challenge=_hashg(json.dumps({
                "commit": commit_pk.y,
                "pk": pk.y,
                }), group.q)
    response = commit_sk.x+challenge*sk.x %group.q 

    bb["clef_curateurs"].append( 
                {"pk": pk.y,
                "zkpproof" :
                    {
                    "commit": commit_pk.y,
                    "response": response
                    },
            })
    return sk
def verify_proof_clef_curateur(G,clef):
    """
    recoit un dictonnaire <clef_curateur>  et le dictionnaire du groupe et verifie la preuve
    """
    pk = clef["pk"] 
    commit = clef["zkpproof"]["commit"] 
    response = clef["zkpproof"]["response"]
    group=elgamal.ElgamalGroup(G["p"],G["g"])
    challenge=_hashg(json.dumps({
                "commit": commit,
                "pk": pk,
                }), group.q)
    if pow(group.g,response,group.p)==commit*pow(pk,challenge,group.p)%group.p:
        return True

    return False  
def combine_clef_curateur(G,clefs):
    """
    combine les clefs curateurs du bb, verifie leurs preuves rend la combinaison 
    sous forme de ElgamalPublickKey
    """
    pk=clefs[0]["pk"]
    group=elgamal.ElgamalGroup(G["p"],G["g"])
    index=0
    for key in clefs:
        assert verify_proof_clef_curateur(G, key),"erreur sur la preuve de la clef du curateur {}".format(index)
        if index!=0:

            pk=pk*key["pk"] %group.p
            
        index+=1
    return elgamal.ElgamalPublicKey(group, pk)    
     

def generate_election(n_curateurs,n_vot,list_del,n_rep, p = None, g = None):
    """
    generer un Json du tableau des bulletins,
    n_curateurs: nb de curateurs sélectionnés pour l'élection
    n_vot: nb de votant
    list_vot: liste de l'id des delegués dans la liste des votants
    p,q: parametre de génération du groupe 
    """
    if p == None or g == None:
        G = elgamal.gen_group()
        p = G.p
        g = G.g
    else:
        G = elgamal.ElGamalGroup(p, g)
    #crée le tableau des bulletins
    bb = generate_empty_bb(p, g)
    #les curateurs générent les clefs e l'elec avec preuve
    bb["clef_curateurs"]=[]
    clefs_privees = [create_clef_curateur_with_proof(bb) for i in range(n_curateurs)]
    #l'admin definit la liste des votants et des delegues, la liste des delegue
    #est une sous-liste de celle des votants
    bb["ids_del"]=list_del
    bb["bulletins_vot"]=np.full((n_rep,n_vot),None)
    bb["sauvegarde"]=np.full((n_rep,n_vot),None)
    bb["parts_dec"]=np.full((n_rep,n_curateurs),None)
    
    #on combine les clefs de curateurs pour former la clef de l'elec
    bb["pk"]=combine_clef_curateur(bb["group"], bb["clef_curateurs"]).y
    return bb, clefs_privees

"""
Phase d'election
"""
def cast_vote_without_proof(bb,vote,id_vot,n_rep):
    """
    a partir du tableau des bulletins bb, du vote et de l'id du votant, poste le vote 
    sans preuve sur le bb, rend l'aléatoire utilisé pour permettre d'ecrire 
    la preuve plus tard
   """
    group=elgamal.ElgamalGroup(bb["group"]["p"],bb["group"]["g"])
    pk=elgamal.ElgamalPublicKey(group,bb["pk"])

    p = group.p
    g = group.g
    q = group.q
    # encrypt
    
    r = group.random_exp()
    c1 = pow(g, r, p)
    c2 = (pow(g, vote, p) * pow(pk.y, r, p)) % p
    ct = (c1, c2)

    bb["bulletins_vot"][n_rep][id_vot]= {
        "ct": {"c1": c1, "c2": c2},
        "zkpproof": None,
        "direct":True,
        }
    return r;
def recast_vote_with_proof(bb,vote,id_vot,r,n_rep):
    def _sort(x, y):
        return (x, y) if vote == 0 else (y, x)
    group=elgamal.ElgamalGroup(bb["group"]["p"],bb["group"]["g"])
    pk=elgamal.ElgamalPublicKey(group,bb["pk"])
    p = group.p
    g = group.g
    q = group.q
    # encrypt
    c1=bb["bulletins_vot"][n_rep][id_vot]["ct"]["c1"]
    c2=bb["bulletins_vot"][n_rep][id_vot]["ct"]["c2"]

    ct = (c1, c2)
    #partie simulée
    e_sim = group.random_exp()
    f_sim = group.random_exp()
    s_sim = (c2*inverse(pow(g, 1-vote, p), p)) % p
    d_sim = (
            (pow(g, f_sim, p)*inverse(pow(c1, e_sim, p), p)) % p,
            (pow(pk.y, f_sim, p)*inverse(pow(s_sim, e_sim, p), p)) % p,
            )
    # partie réelle
    z = group.random_exp()
    d_true = (pow(g, z, p), pow(pk.y, z, p))
    e = _hashg(json.dumps({
            #"ct": {"c1": c1, "c2": c2},
            "commit": _sort(d_true, d_sim),
            #"pk": pk.y,
            }), q)
    e_true = (e - e_sim) % q
    f_true = (r*e_true + z) % q

    bb["bulletins_vot"][n_rep][id_vot]= {
        "ct": {"c1": c1, "c2": c2},
        "zkpproof": {
            "commit": _sort(d_true, d_sim),
            "challenge": _sort(e_true, e_sim),
            "response": _sort(f_true, f_sim),
            },
        "direct":True,
        }  
    
def cast_vote_with_proof(bb,vote,id_vot,n_rep):
    
    """
    envoie le bulletin de vote sur bb, si le vote vient un delegué, partage l'aléatoire
    
    """
    group=elgamal.ElgamalGroup(bb["group"]["p"],bb["group"]["g"])
    pk=elgamal.ElgamalPublicKey(group,bb["pk"])
    
    def _sort(x, y):
        return (x, y) if vote == 0 else (y, x)
    p = group.p
    g = group.g
    q = group.q
    # encrypt

    r = group.random_exp()
    c1 = pow(g, r, p)
    c2 = (pow(g, vote, p) * pow(pk.y, r, p)) % p
    ct = (c1, c2)
    #partie simulée
    e_sim = group.random_exp()
    f_sim = group.random_exp()
    s_sim = (c2*inverse(pow(g, 1-vote, p), p)) % p
    d_sim = (
            (pow(g, f_sim, p)*inverse(pow(c1, e_sim, p), p)) % p,
            (pow(pk.y, f_sim, p)*inverse(pow(s_sim, e_sim, p), p)) % p,
            )
    # partie réelle
    z = group.random_exp()
    d_true = (pow(g, z, p), pow(pk.y, z, p))
    e = _hashg(json.dumps({
            #"ct": {"c1": c1, "c2": c2},
            "commit": _sort(d_true, d_sim),
            #"pk": pk.y,
            }), q)
    e_true = (e - e_sim) % q
    f_true = (r*e_true + z) % q

    bb["bulletins_vot"][n_rep][id_vot]= {
        "ct": {"c1": c1, "c2": c2},
        "zkpproof": {
            "commit": _sort(d_true, d_sim),
            "challenge": _sort(e_true, e_sim),
            "response": _sort(f_true, f_sim),
            },
        "direct":True,
        }
    

def copy_vote_without_proof(bb,id_copie,id_vote,n_rep):
    """update le bb avec la copie d'un vote d'un délégué, la preuve de vote n'est pas 
    publiée.
    id_copie: la positiion du vote copié
    id_vote: la position de la copie
    retourne z l'aléatoire utilisé pour le masquage"""
    group=elgamal.ElgamalGroup(bb["group"]["p"],bb["group"]["g"])
    pk=elgamal.ElgamalPublicKey(group,bb["pk"])
    # verifie si le vote copié est valide
    assert id_copie in bb["ids_del"],"essai de copie d'un vote d'un non-délégué"
    assert bb["bulletins_vot"][n_rep][id_copie]!=None,"essai de copie de vote pas encore effectué"
    c2=bb["bulletins_vot"][n_rep][id_copie]["ct"]["c2"]
    c1=bb["bulletins_vot"][n_rep][id_copie]["ct"]["c1"]
    z=choice(range(0, group.p - 1))
    copie_c1=c1*pow(group.g, z, group.p)%group.p
    copie_c2=c2*pow(bb["pk"], z, group.p)%group.p
    #besoin que le challenge soit le hash du commit uniquement
    ballot={
        "ct": {"c1": copie_c1, "c2": copie_c2},
        "zkproof": None,
        "direct":False,
        }
    bb["bulletins_vot"][n_rep][id_vote]=ballot
    return z

def recopy_vote_with_proof(bb,id_copie,id_vote,z,n_rep):
    """ 
    Prend un bulletin de vote envoyé sans preuve et l'aléatoire utilisé pour le masquer
    et poste sur le bb le bulletin avec la preuve ajoutée
    bb: tableau des bulletins
    id_vote: emplacement du vote
    id_copie: emplacement du vote copié
    z: aléatoire qui a été utilisé pour masquer la copie
    """
    group=elgamal.ElgamalGroup(bb["group"]["p"],bb["group"]["g"])
    pk=elgamal.ElgamalPublicKey(group,bb["pk"])
    p = group.p
    g = group.g
    q = group.q
    # encrypt
    Aprime=bb["bulletins_vot"][n_rep][id_vote]["ct"]["c1"]
    Bprime=bb["bulletins_vot"][n_rep][id_vote]["ct"]["c2"]
    #recuperer de tout les ct des del
    c1_del=[bb["bulletins_vot"][n_rep][id_c]["ct"]["c1"] for id_c in bb["ids_del"]]
    c2_del=[bb["bulletins_vot"][n_rep][id_c]["ct"]["c2"] for id_c in bb["ids_del"]]
    
    
    #calcul de la preuve
    #preuve simulée
    
    e_sim=  [group.random_exp() for i in bb["ids_del"]]
    f_sim = [group.random_exp() for i in bb["ids_del"]]
    posréel=0
    commit =[None]*len(bb["ids_del"])
    index=0
    for i in bb["ids_del"]:
        if i==id_copie:
            posréel=index
        AsurA=Aprime*inverse(c1_del[index],p)
        BsurB=Bprime*inverse(c2_del[index],p)
        commit[index] = (
                (pow(g, f_sim[index], p)*inverse(pow(AsurA, e_sim[index], p), p)) % p,
                (pow(pk.y, f_sim[index], p)*inverse(pow(BsurB, e_sim[index], p), p)) % p,
                )
        index+=1

    # partie réelle
    s = group.random_exp()
    a_true = (pow(g, s, p), pow(pk.y, s, p))
    commit[posréel]=a_true
    e = _hashg(json.dumps({
            #"ct": {"c1": c1, "c2": c2},
            "commit": commit,
            #"pk": pk.y,
            }), q)
    e_true=e
    for i in range(len(bb["ids_del"])):
        if i!=posréel:
            e_true=e_true-e_sim[i]
    e_sim[posréel]=e_true
    f_true = (z*e_true + s) % q
    f_sim[posréel]=f_true

    bb["bulletins_vot"][n_rep][id_vote]= {
        "ct": {"c1": Aprime, "c2": Bprime},
        "zkpproof": {
            "commit": commit,
            "challenge": e_sim,
            "response": f_sim,
            },
        "direct":False,
        }
    

    
    
def copy_vote_with_proof(bb,id_copie,id_vote,n_rep):
    """update le bb avec la copie d'un vote d'un délégué, la preuve est indistinguable
      id_copie, la position du vote copié dans le bb[ballot]
      id_vote, la position de vote
      """

    group=elgamal.ElgamalGroup(bb["group"]["p"],bb["group"]["g"])
    pk=elgamal.ElgamalPublicKey(group,bb["pk"])
    # verifie si le vote copié est valide
    assert id_copie in bb["ids_del"],"essai de copie d'un vote d'un non-délégué"

    assert bb["bulletins_vot"][n_rep][id_copie]!=None,"essai de copie de vote pas encore effectué"
    
    p = group.p
    g = group.g
    q = group.q
    #calcul de ct du vote copié
    c2_initial=bb["bulletins_vot"][n_rep][id_copie]["ct"]["c2"]
    c1_initial=bb["bulletins_vot"][n_rep][id_copie]["ct"]["c1"]
    z=choice(range(0, group.p - 1))
    Aprime=c1_initial*pow(group.g, z, group.p)%group.p
    Bprime=c2_initial*pow(bb["pk"], z, group.p)%group.p
    ct = (Aprime, Bprime)
    
    #recuperer de tout les ct des del
    for id_c in bb["ids_del"]:
        assert  bb["bulletins_vot"][n_rep][id_c]!=None, "la phase de vote des délégués sans preuve n'est pas encore finie"
    c1_del=[bb["bulletins_vot"][n_rep][id_c]["ct"]["c1"] for id_c in bb["ids_del"]]
    c2_del=[bb["bulletins_vot"][n_rep][id_c]["ct"]["c2"] for id_c in bb["ids_del"]]
    
    
    #calcul de la preuve
    #preuve simulée
    
    e_sim=  [group.random_exp() for i in bb["ids_del"]]
    f_sim = [group.random_exp() for i in bb["ids_del"]]
    posréel=0
    commit =[None]*len(bb["ids_del"])
    index=0
    for i in bb["ids_del"]:
        if i==id_copie:
            posréel=index
        AsurA=Aprime*inverse(c1_del[index],p)
        BsurB=Bprime*inverse(c2_del[index],p)
        commit[index] = (
                (pow(g, f_sim[index], p)*inverse(pow(AsurA, e_sim[index], p), p)) % p,
                (pow(pk.y, f_sim[index], p)*inverse(pow(BsurB, e_sim[index], p), p)) % p,
                )
        index+=1

    # partie réelle
    s = group.random_exp()
    a_true = (pow(g, s, p), pow(pk.y, s, p))
    commit[posréel]=a_true
    e = _hashg(json.dumps({
            #"ct": {"c1": c1, "c2": c2},
            "commit": commit,
            #"pk": pk.y,
            }), q)
    e_true=e
    for i in range(len(bb["ids_del"])):
        if i!=posréel:
            e_true=e_true-e_sim[i]
    e_sim[posréel]=e_true
    f_true = (z*e_true + s) % q
    f_sim[posréel]=f_true

    bb["bulletins_vot"][n_rep][id_vote]= {
        "ct": {"c1": Aprime, "c2": Bprime},
        "zkpproof": {
            "commit": commit,
            "challenge": e_sim,
            "response": f_sim,
            },
        "direct":False,
        }
    
def verify_proof_vote(G,pk,ballot,bb,n_rep):
    
    """
    verifie si la preuve lié au ballot sur le bb est correcte.
    return true si c'est le cas
    """
    group=elgamal.ElgamalGroup(G["p"],G["g"])
    pk=elgamal.ElgamalPublicKey(group,pk)
    if ballot["direct"]==True:
        assert len(ballot["zkpproof"]["challenge"])==2,"un ballot est référencé en direct alors qu'il est indirect"
        e = _hashg(json.dumps({
            #"ct": ballot["ct"],
            "commit": ballot["zkpproof"]["commit"],
            #"pk": pk.y,
            }), group.q)
        if (sum(ballot["zkpproof"]["challenge"]) % group.q != e):
            return False
        for s in range(2):
            f = ballot["zkpproof"]["response"][s]
            (d1, d2) = ballot["zkpproof"]["commit"][s]
            e = ballot["zkpproof"]["challenge"][s]
            c1 = ballot["ct"]["c1"]
            c2 = ballot["ct"]["c2"]
            if s == 1:
                c2 = (c2 * inverse(group.g, group.p)) % group.p
            if (pow(group.g,f, group.p) != (d1 * pow(c1, e, group.p)) % group.p or
                    pow(pk.y, f, group.p) != (d2 * pow(c2, e, group.p)) % group.p):
                return False
        return True
    if ballot["direct"]==False:
        
        Aprime=ballot["ct"]["c1"]
        Bprime=ballot["ct"]["c2"]
        commit=ballot["zkpproof"]["commit"]
        assert len(commit)==len(bb["ids_del"]),"un ballot est référencé en indirect alors qu'il est direct"
        et=ballot["zkpproof"]["challenge"]
        ft=ballot["zkpproof"]["response"]
        c1_del=[bb["bulletins_vot"][n_rep][id_c]["ct"]["c1"] for id_c in bb["ids_del"]]
        c2_del=[bb["bulletins_vot"][n_rep][id_c]["ct"]["c2"] for id_c in bb["ids_del"]]
        #verifier somme ei = E
        E = _hashg(json.dumps({
            #"ct": ballot["ct"],
            "commit": ballot["zkpproof"]["commit"],
            #"pk": pk.y,
            }), group.q)
        if (sum(et)%group.q!=E):

            return False
        #verifier gf et pkf
        index=0
        
        for i in range(len(bb["ids_del"])):
            
            f=ft[index]
            (a1,a2)=commit[index]
            e=et[index]
            AsurA=Aprime*inverse(c1_del[index],group.p)
            BsurB=Bprime*inverse(c2_del[index],group.p)
            if (pow(group.g,f, group.p) != (a1 * pow(AsurA, e, group.p)) % group.p or
                    pow(pk.y, f, group.p) != (a2 * pow(BsurB, e, group.p)) % group.p):
                return False
        return True

def save_before_proof(bb,n_rep):
    for i in bb["ids_del"]:
        bb["sauvegarde"][n_rep][i]=bb["bulletins_vot"][n_rep][i]["ct"]
def verify_after_proof(bb,n_rep):
    for i in bb["ids_del"]:
        assert bb["sauvegarde"][n_rep][i]==bb["bulletins_vot"][n_rep][i]["ct"],"le délégué {} a changé son chiffré lors du recast".format(i)
     
            
"""
Phase post-élection
"""

def combine_vote(bb,n_rep):
    
    """
    recoit le bulletin de vote et rend la combinaison des votes
    """
    group=elgamal.ElgamalGroup(bb["group"]["p"],bb["group"]["g"])
    
    
    public_key=elgamal.ElgamalPublicKey(group,bb["pk"])
    encrypted_tally=elgamal.ElgamalCiphertext(group,bb["bulletins_vot"][n_rep][0]["ct"]["c1"],bb["bulletins_vot"][n_rep][0]["ct"]["c2"])
    index=0
    for ballot in bb["bulletins_vot"][n_rep]:
        
        if ballot==None:
            continue
        
        ct=elgamal.ElgamalCiphertext(group,ballot["ct"]["c1"],ballot["ct"]["c2"])
        #on verifie que la preuve n'est pas mauvaise
        assert verify_proof_vote(bb["group"],bb["pk"],ballot,bb,n_rep),"erreur sur le preuve du ballot numero {}".format(index)
        #on vérifie que le délégué a bien partagé son aléatoire

        if index!=0:

            encrypted_tally=encrypted_tally.homomorphic_add(ct)

        index+=1
    return encrypted_tally
def cast_part_dec_with_proof(bb,ct_res,sk_curateur,n_rep,id_del):
    """
    crée la part de dechiffrement d'un curateur du résultat de l'élection et
    la poste sur le bb avec sa zkp
    ct_res:cipher du résultat sous forme ElgamalCiphertext
    sk_curateur:clef secrete  du curateur  sous forme ElgamalSecretKey
    """
    pk = sk_curateur.pk()
    G=sk_curateur.G
    c1 = ct_res.c1
    
    group=ct_res.G
    df = pow(ct_res.c1,sk_curateur.x,G.p) % G.p 
    s=choice(range(0, group.q-1))
    commit = [pow(group.g,s,group.p),pow(c1,s,group.p)]

    challenge=_hashg(json.dumps({
                    " pk ": pk.y,
                    " c1 ": c1,
                    " part_dec ": df ,
                    " commit ": commit 
                    }), group.q)
    response = s+challenge*sk_curateur.x % group.q
    bb["parts_dec"][n_rep][id_del]={"pk": pk.y,
            "c1": c1,
            "part_dec": df,
            "zkpproof" : {
                "commit": commit,
                "response": response
                }
            }    
    
    
def verify_proof_dec(part_dec,G,n_rep):
    """
    recoit un dic part_dec et de sa preuve et le groupe de l'éleciton,
    rend la validité de la preuve
    """
    group=elgamal.ElgamalGroup(G["p"],G["g"])
    pk = part_dec["pk"]
    c1 = part_dec["c1"]
    df = part_dec["part_dec"]
    commit = part_dec["zkpproof"]["commit"]
    response = part_dec["zkpproof"]["response"]
    
    challenge=_hashg(json.dumps({
                " pk ": pk,
                " c1 ": c1,
                " part_dec ": df ,
                " commit ": commit 
                }), group.q)
    # Verify the proof

    if pow(group.g,response,group.p)== commit[0]*pow(pk,challenge,group.p)%group.p:
        if pow(c1,response,group.p)== commit[1]*pow(df,challenge,group.p)%group.p:
            return True
        

        
        return False

def combine_decryption_factors(bb,n_rep):
    """
    Recoit le tableau des bulletins bb avec la part de déchiffrement et
    renvoie le résultat de l'élection
    """

    ct_res=combine_vote(bb,n_rep)
    group=elgamal.ElgamalGroup(bb["group"]["p"],bb["group"]["g"])
        
    #fusion partiel decryption 
    df=bb["parts_dec"][n_rep][0]["part_dec"]
    
    index=1
    for part_dec in bb["parts_dec"][n_rep]:
        
        assert verify_proof_dec(part_dec, bb["group"],n_rep),"erreur dans la preuve de part de déchiffrement {}".format(index)
        if index!=1:     
            df=df*part_dec["part_dec"] % group.p
        index+=1
        
    res = ct_res.c2*inverse(df,group.p)%group.p
    
    return res
def tally(bb,n_rep):
    """
    recoit un dic part_dec et de sa preuve et le groupe de l'éleciton,
    rend la validité de la preuve
    """
    g_m=combine_decryption_factors(bb,n_rep)
    
    group=elgamal.ElgamalGroup(bb["group"]["p"],bb["group"]["g"])
    m = elgamal.dLog(group.p, group.g, g_m)
    index=1
    for df in bb["parts_dec"][n_rep]:
        assert verify_proof_dec(df,bb["group"],n_rep),"erreur sur la preuve de part de chiffrement {}".format(index)
        if verify_proof_dec(df,bb["group"],n_rep)==False:
        
            return None
        index+=1
    return m
    

"""
Simulation d'une élection

"""

nb_votant=10
nb_delegue=3
id_delegue=random.sample(range(0,nb_votant),nb_delegue)
n_curateurs=3
n_rep=3
n_direct_v=4
n_inderect_v=3
start=timer()
n_direct_d=1.
n_inderct_d=2
### procède a la cérémonie de création de clef de l'election et genere le tableu des bulletins
bb,sk=generate_election(n_curateurs,nb_votant,id_delegue,n_rep)
end=timer()
print(end-start)


### phase de vote des délégués sans preuve
#cast_vote(bb,vote,id_vote)

for j in range(n_rep):
    r=[None]*nb_delegue
    vote=[None]*nb_delegue
    index=0
    delegue=0
    #phase de vote des délégués sans preuve
    for i in id_delegue:
        
        if delegue <n_direct_d:
            
            vote[index]=int(random.randint(0,1))
            r[index]=cast_vote_without_proof(bb,vote[index],i, j)
            
            delegue+=1
        else:
            if delegue==1:
                vote[index]=0
            else:
                vote[index]=choice(range(0,delegue-1))
            
            r[index]=copy_vote_without_proof(bb,id_delegue[vote[index]],i,j)
            delegue+=1
        index+=1
    save_before_proof(bb,j)
    index=0
    delegue=0
    #phase de vote des délégués avec preuve
    for i in id_delegue:
        if delegue<n_direct_d:
            recast_vote_with_proof(bb,vote[index],i,r[index],j)
            delegue+=1
        else:
            
            recopy_vote_with_proof(bb,id_delegue[vote[index]],i,r[index],j)
            delegue+=1
        index+=1
    verify_after_proof(bb,j)
            
    #phase de vote des votant
    direct=0
    for i in range(nb_votant):
        if i in id_delegue:
            continue
        #votant direct
        if direct <n_direct_v:
            cast_vote_with_proof(bb, random.randint(0,1), i, j)
            direct+=1
        else:
            #votants indirect
            id_copie=choice(id_delegue)
            copy_vote_with_proof(bb, id_copie, i,j)
    ct_res=combine_vote(bb,j)
    for i in range(n_curateurs):
        cast_part_dec_with_proof(bb,ct_res,sk[i],j,i)
    print("résultat:")
    print(tally(bb,j))


