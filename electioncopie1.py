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
                "pk": pk,
                }), group.q)
    response = commit_sk.x+challenge*sk.x %group.q 

    bb["clef_curateurs"].append( 
                {"pk": pk,
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
    group=elgamal.ElGamalGroup(G["p"],G["g"])
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
    pk=clefs["pk"][0]
    group=elgamal.ElGamalGroup(G["p"],G["g"])
    index=0
    for key in clefs:
        assert verify_proof_clef_curateur(G, key),"erreur sur la preuve de la clef du curateur {}".format(index)
        if index!=0:

            pk=pk*key["pk"] %group.p
            
        index+=1
    return elgamal.ElgamalPublicKey(group, pk)    
     

def generate_election(n_curateurs,n_vot,n_del, p = None, g = None):
    if p == None or g == None:
        G = elgamal.gen_group()
        p = G.p
        g = G.g
    else:
        G = elgamal.ElGamalGroup(p, g)
    #crée le tableau des bulletins
    bb = generate_empty_bb(p, g)
    #les curateurs générent les clefs e l'elec avec preuve
    clefs_privees = [create_clef_curateur_with_proof(bb) for i in range(n_curateurs)]
    #l'admin definit la liste des votants et des delegues, la liste des delegue
    #est une sous-liste de celle des votants
    bb["ids_vot"]=range(0,n_vot)
    bb["ids_del"]=range(0,n_del)
    #on combine les clefs de curateurs pour former la clef de l'elec
    combine_clef_curateur(G, bb["clef_curateurs"])
    return bb, clefs_privees
"""
Phase d'election
"""


def cast_vote_with_proof(bb,vote,id_vot,delegue):
    
    """
    envoie le bulletin de vote sur bb, si le vote vient un delegué, partage l'aléatoire
    
    """
    group=elgamal.ElgamalGroup(bb["group"]["p"],bb["group"]["g"])
    pk=elgamal.ElgamalPublicKey(group,bb["pk"])
    
    def _sort(x, y):
        return (x, y) if m == 0 else (y, x)
    p = group.p
    g = group.g
    q = group.q
    # encrypt
    # We cannot use pk.encrypt(m) since we need to know the randomness used.
    r = group.random_exp()
    c1 = pow(g, r, p)
    c2 = (pow(g, m, p) * pow(pk.y, r, p)) % p
    ct = (c1, c2)
    #partie simulée
    e_sim = group.random_exp()
    f_sim = group.random_exp()
    s_sim = (c2*inverse(pow(g, 1-m, p), p)) % p
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
    bb["bulletin_vot"][id_vot]= {
        "ct": {"c1": c1, "c2": c2},
        "zkpproof": {
            "commit": _sort(d_true, d_sim),
            "challenge": _sort(e_true, e_sim),
            "response": _sort(f_true, f_sim),
            },
        "id_votant":id_votant,
        "aléatoire":aléatoire,
        }    
def copy_vote_with_proof(bb,id_vote_copie,id_vote,delegue):
    "update le bb avec la copie d'un vote d'un délégué, la preuve est indistinguable"
    "id_copie, la position du vote dans le bb[ballot]"
    group=elgamal.ElgamalGroup(bb["group"]["p"],bb["group"]["g"])
    z=randint(0, group.p - 1)
    c1=bb["ballots"][id_copie]["ct"]["c1"]
    c2=bb["ballots"][id_copie]["ct"]["c2"]
    preuve=bb["ballots"][id_copie]["dproof"]
    copie_c1=c1*pow(group.g, z, group.p)%group.p
    copie_c2=c2*pow(bb["pk"], z, group.p)%group.p
    #besoin que le challenge soit le hash du commit uniquement
    ballot={
        "ct": {"c1": copie_c1, "c2": copie_c2},
        "dproof": {
            "commit": preuve["commit"],
            "challenge": preuve["challenge"],
            "response": ((preuve["response"][0]+preuve["challenge"][0]*z)%group.q,(preuve["response"][1]+preuve["challenge"][1]*z)%group.q),
            }
        }
    bb["ballots"].append(ballot)  
def verify_proof_vote(G,pk,ballot):
    """
    verifie si la preuve lié au ballot sur le bb est correcte.
    return true si c'est le cas
    """
    group=elgamal.ElGamalGroup(G["p"],G["g"])
    public_key=elgamal.ElgamalPublicKey(group,bb["pk"])
    e = _hashg(json.dumps({
        #"ct": ballot["ct"],
        "commit": ballot["dproof"]["commit"],
        #"pk": pk.y,
        }), q)
    if (sum(ballot["dproof"]["challenge"]) % q != e):
        return False
    for s in range(2):
        f = ballot["dproof"]["response"][s]
        (d1, d2) = ballot["dproof"]["commit"][s]
        e = ballot["dproof"]["challenge"][s]
        c1 = ballot["ct"]["c1"]
        c2 = ballot["ct"]["c2"]
        if s == 1:
            c2 = (c2 * inverse(g, p)) % p
        if (pow(g, f, p) != (d1 * pow(c1, e, p)) % p or
                pow(pk.y, f, p) != (d2 * pow(c2, e, p)) % p):
            return False
    return True



def combine_vote():
    
    