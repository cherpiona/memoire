# -*- coding: utf-8 -*-
"""
Created on Mon Aug  8 05:34:03 2022

@author: moi
"""
import json
import hashlib
import canonicaljson
import elgamal
from random import randint
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
    return {"group": {"p": p, "g": g}, "ballots": []}
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
     

def generate_election(n_curateurs,n_vot,list_del, p = None, g = None):
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
    bb["bulletins_vot"]=[None]*n_vot
    bb["parts_dec"]=[]
    
    #on combine les clefs de curateurs pour former la clef de l'elec
    bb["pk"]=combine_clef_curateur(bb["group"], bb["clef_curateurs"]).y
    return bb, clefs_privees

"""
Phase d'election
"""
def cast_vote_without_proof(bb,vote,id_vot):
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

    bb["bulletins_vot"][id_vot]= {
        "ct": {"c1": c1, "c2": c2},
        "zkpproof": None,
        "direct":True,
        }
    return r;
def recast_vote_with_proof(bb,vote,id_vot,r):
    def _sort(x, y):
        return (x, y) if vote == 0 else (y, x)
    group=elgamal.ElgamalGroup(bb["group"]["p"],bb["group"]["g"])
    pk=elgamal.ElgamalPublicKey(group,bb["pk"])
    p = group.p
    g = group.g
    q = group.q
    # encrypt
    
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

    bb["bulletins_vot"][id_vot]= {
        "ct": {"c1": c1, "c2": c2},
        "zkpproof": {
            "commit": _sort(d_true, d_sim),
            "challenge": _sort(e_true, e_sim),
            "response": _sort(f_true, f_sim),
            },
        "direct":True,
        }  
    
def cast_vote_with_proof(bb,vote,id_vot):
    
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
    # We cannot use pk.encrypt(m) since we need to know the randomness used.
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
    aléatoire=None
    if delegue==True:
        aléatoire=r
    bb["bulletins_vot"][id_vot]= {
        "ct": {"c1": c1, "c2": c2},
        "zkpproof": {
            "commit": _sort(d_true, d_sim),
            "challenge": _sort(e_true, e_sim),
            "response": _sort(f_true, f_sim),
            },
        "direct":True,
        }
    

def copy_vote_without_proof(bb,id_copie,id_vote):
    """update le bb avec la copie d'un vote d'un délégué, la preuve de vote n'est pas 
    publiée.
    id_copie: la positiion du vote copié
    id_vote: la position de la copie"""
    group=elgamal.ElgamalGroup(bb["group"]["p"],bb["group"]["g"])
    pk=elgamal.ElgamalPublicKey(group,bb["pk"])
    # verifie si le vote copié est valide
    assert id_copie in bb["ids_del"],"essai de copie d'un vote d'un non-délégué"
    assert bb["bulletins_vot"][id_copie]!=None,"essai de copie de vote pas encore effectué"
    c2=bb["bulletins_vot"][id_copie]["ct"]["c2"]
    c1=bb["bulletins_vot"][id_copie]["ct"]["c1"]
    z=randint(0, group.p - 1)
    copie_c1=c1*pow(group.g, z, group.p)%group.p
    copie_c2=c2*pow(bb["pk"], z, group.p)%group.p
    #besoin que le challenge soit le hash du commit uniquement
    ballot={
        "ct": {"c1": copie_c1, "c2": copie_c2},
        "zkproof": None,
        "direct":False,
        }
    bb["bulletins_vot"]["id_vote"]=ballot

def copy_vote_with_proof(bb,id_copie,id_vote):
    "update le bb avec la copie d'un vote d'un délégué, la preuve est indistinguable"
    "id_copie, la position du vote copié dans le bb[ballot]"
    group=elgamal.ElgamalGroup(bb["group"]["p"],bb["group"]["g"])
    pk=elgamal.ElgamalPublicKey(group,bb["pk"])
    # verifie si le vote copié est valide
    assert id_copie in bb["ids_del"],"essai de copie d'un vote d'un non-délégué"
    assert bb["bulletins_vot"][id_copie]!=None,"essai de copie de vote pas encore effectué"
    
    c2=bb["bulletins_vot"][id_copie]["ct"]["c2"]
    aléatoire=bb["bulletins_vot"][id_copie]["aléatoire"]
    #calcul de m du vote copié
    g_m =  (c2 * inverse(pow(pk.y, aléatoire, group.p), group.p)) % group.p
    m = elgamal.dLog(group.p, group.g, g_m)

def verify_proof_vote(G,pk,ballot):
    
    """
    verifie si la preuve lié au ballot sur le bb est correcte.
    return true si c'est le cas
    """
    group=elgamal.ElgamalGroup(G["p"],G["g"])
    pk=elgamal.ElgamalPublicKey(group,pk)
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
"""
Phase post-élection
"""

def combine_vote(bb):
    
    """
    recoit le bulletin de vote et rend la combinaison des votes
    """
    group=elgamal.ElgamalGroup(bb["group"]["p"],bb["group"]["g"])
    
    
    public_key=elgamal.ElgamalPublicKey(group,bb["pk"])
    encrypted_tally=elgamal.ElgamalCiphertext(group,bb["bulletins_vot"][0]["ct"]["c1"],bb["bulletins_vot"][0]["ct"]["c2"])
    index=0
    for ballot in bb["bulletins_vot"]:
        
        if ballot==None:
            continue
        
        ct=elgamal.ElgamalCiphertext(group,ballot["ct"]["c1"],ballot["ct"]["c2"])
        #on verifie que la preuve n'est pas mauvaise
        assert verify_proof_vote(bb["group"],bb["pk"],ballot),"erreur sur le preuve du ballot numero {}".format(index)
        #on vérifie que le délégué a bien partagé son aléatoire
        assert not(ballot["aléatoire"]==None and index in bb["ids_del"]),"le délégué {} a oublié de partager son aléatoire".format(index)
 
        #on vérifie que seul les délégués ont partagé leur aléatoire
        assert not(ballot["aléatoire"]!=None and index not in bb["ids_del"]),"le votant {} a essayé de partager son aléatoire".format(index)
        if index!=0:

            encrypted_tally=encrypted_tally.homomorphic_add(ct)

        index+=1
    return encrypted_tally
def cast_part_dec_with_proof(bb,ct_res,sk_curateur):
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
    s=randint(0, group.q-1)
    commit = [pow(group.g,s,group.p),pow(c1,s,group.p)]

    challenge=_hashg(json.dumps({
                    " pk ": pk.y,
                    " c1 ": c1,
                    " part_dec ": df ,
                    " commit ": commit 
                    }), group.q)
    response = s+challenge*sk_curateur.x % group.q
    bb["parts_dec"].append({"pk": pk.y,
            "c1": c1,
            "part_dec": df,
            "zkpproof" : {
                "commit": commit,
                "response": response
                }
            }    
    )
    
def verify_proof_dec(part_dec,G):
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

def combine_decryption_factors(bb):
    """
    Recoit le tableau des bulletins bb avec la part de déchiffrement et
    renvoie le résultat de l'élection
    """

    ct_res=combine_vote(bb)
    group=elgamal.ElgamalGroup(bb["group"]["p"],bb["group"]["g"])
        
    #fusion partiel decryption 
    df=bb["parts_dec"][0]["part_dec"]
    
    index=1
    for part_dec in bb["parts_dec"]:
        
        assert verify_proof_dec(part_dec, bb["group"]),"erreur dans la preuve de part de déchiffrement {}".format(index)
        if index!=1:     
            df=df*part_dec["part_dec"] % group.p
        index+=1
        
    res = ct_res.c2*inverse(df,group.p)%group.p
    
    return res
def tally(bb):
    """
    recoit un dic part_dec et de sa preuve et le groupe de l'éleciton,
    rend la validité de la preuve
    """
    g_m=combine_decryption_factors(bb)
    
    group=elgamal.ElgamalGroup(bb["group"]["p"],bb["group"]["g"])
    m = elgamal.dLog(group.p, group.g, g_m)
    index=1
    for df in bb["parts_dec"]:
        assert verify_proof_dec(df,bb["group"]),"erreur sur la preuve de part de chiffrement {}".format(index)
        if verify_proof_dec(df,bb["group"])==False:
        
            return None
        index+=1
    return m
    

"""
Simulation d'une élection
"""
### procède a la cérémonie de création de clef de l'election et genere le tableu des bulletins
bb,sk=generate_election(3,6,[0,1,2])

### phase de vote des délégués
cast_vote_with_proof(bb, 0,0, True)
cast_vote_with_proof(bb, 1,1, True)
copy_vote_with_proof(bb,1,2,True)
### phase de vote des votants
#cast_vote_with_proof(bb,1,2,True)
cast_vote_with_proof(bb, 0,3,False)
cast_vote_with_proof(bb,1,4,False)
copy_vote_with_proof(bb, 2, 5)
#copy_vote_with_proof(bb,4,3)
###post-elec, les curateurs font les part de dechiffrement
ct_res=combine_vote(bb)
cast_part_dec_with_proof(bb,ct_res,sk[0])
cast_part_dec_with_proof(bb,ct_res,sk[1])
cast_part_dec_with_proof(bb,ct_res,sk[2])
###
print(tally(bb))





