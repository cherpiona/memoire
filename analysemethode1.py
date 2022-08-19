# -*- coding: utf-8 -*-
"""
Created on Mon Aug  8 05:34:03 2022

@author: moi
"""
import json
import hashlib
import canonicaljson
import elgamal
from secrets import randbelow,choice
import numpy as np
import random
from timeit import default_timer as timer
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
import csv
from scipy.interpolate import griddata

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


def cast_vote_with_proof(bb,vote,id_vot,n_rep,delegue=False):
    
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
    aléatoire=None
    if delegue==True:
        aléatoire=r
    bb["bulletins_vot"][n_rep][id_vot]= {
        "ct": {"c1": c1, "c2": c2},
        "zkpproof": {
            "commit": _sort(d_true, d_sim),
            "challenge": _sort(e_true, e_sim),
            "response": _sort(f_true, f_sim),
            },
        "aléatoire":aléatoire,
        }    
def copy_vote_with_proof(bb,id_copie,id_vote,n_rep,delegue=False):
    "update le bb avec la copie d'un vote d'un délégué, la preuve est indistinguable"
    "id_copie, la position du vote copié dans le bb[ballot]"
    group=elgamal.ElgamalGroup(bb["group"]["p"],bb["group"]["g"])
    pk=elgamal.ElgamalPublicKey(group,bb["pk"])
    # verifie si le vote copié est valide
    assert id_copie in bb["ids_del"],"essai de copie d'un vote d'un non-délégué"
    assert bb["bulletins_vot"][n_rep][id_copie]!=None,"essai de copie de vote pas encore effectué"
    
    c2=bb["bulletins_vot"][n_rep][id_copie]["ct"]["c2"]
    aléatoire=bb["bulletins_vot"][n_rep][id_copie]["aléatoire"]
    #calcul de m du vote copié
    g_m =  (c2 * inverse(pow(pk.y, aléatoire, group.p), group.p)) % group.p
    m = elgamal.dLog(group.p, group.g, g_m)

    #calcul du nouveau preuve
    cast_vote_with_proof(bb, m, id_vote,n_rep, delegue)  
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
        assert verify_proof_vote(bb["group"],bb["pk"],ballot),"erreur sur le preuve du ballot numero {}".format(index)
        #on vérifie que le délégué a bien partagé son aléatoire
        assert not(ballot["aléatoire"]==None and index in bb["ids_del"]),"le délégué {} a oublié de partager son aléatoire".format(index)
 
        #on vérifie que seul les délégués ont partagé leur aléatoire
        assert not(ballot["aléatoire"]!=None and index not in bb["ids_del"]),"le votant {} a essayé de partager son aléatoire".format(index)
        if index!=0:

            encrypted_tally=encrypted_tally.homomorphic_add(ct)

        index+=1
    return encrypted_tally
def cast_part_dec_with_proof(bb,ct_res,sk_curateur,n_rep,id_curateur):
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
    bb["parts_dec"][n_rep][id_curateur]={"pk": pk.y,
            "c1": c1,
            "part_dec": df,
            "zkpproof" : {
                "commit": commit,
                "response": response
                }
            }    
    
    
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

def combine_decryption_factors(bb,n_rep):
    """
    Recoit le tableau des bulletins bb avec la part de déchi ffrement et
    renvoie le résultat de l'élection
    """

    ct_res=combine_vote(bb,n_rep)
    group=elgamal.ElgamalGroup(bb["group"]["p"],bb["group"]["g"])
        
    #fusion partiel decryption 
    df=bb["parts_dec"][n_rep][0]["part_dec"]
    
    index=1
    for part_dec in bb["parts_dec"][n_rep]:
        
        assert verify_proof_dec(part_dec, bb["group"]),"erreur dans la preuve de part de déchiffrement {}".format(index)
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
        assert verify_proof_dec(df,bb["group"]),"erreur sur la preuve de part de chiffrement {}".format(index)
        if verify_proof_dec(df,bb["group"])==False:
        
            return None
        index+=1
    return m
    

"""
Simulation d'une élection
"""
### procède a la cérémonie de création de clef de l'election et genere le tableu des bulletins
nb_iter=3
rendudelegue=np.linspace(1,300,nb_iter,dtype=int)
votants=np.linspace(1,3000,nb_iter,dtype=int)

temps=np.full((nb_iter,nb_iter),None)

for rdi in range(nb_iter):
    
    for rvi in range(nb_iter):
        start=timer()
        nb_delegue=rendudelegue[rdi]
        nb_votant_classique=votants[rvi]
        nb_votant_total=nb_delegue+nb_votant_classique
        
        id_delegue=random.sample(range(0,nb_votant_total),nb_delegue)
        n_curateurs=5
        n_rep=3
        n_direct_v=int(nb_votant_classique/2)+1
        n_inderect_v=nb_votant_classique-n_direct_v
        
        n_direct_d=int(nb_delegue/2)+1
        n_inderct_d=nb_delegue-n_direct_d
        ### procède a la cérémonie de création de clef de l'election et genere le tableu des bulletins
        bb,sk=generate_election(n_curateurs,nb_votant_total,id_delegue,n_rep)
        
        
        
        
        
        ### phase de vote des délégués sans preuve
        #cast_vote(bb,vote,id_vote)
        
        for j in range(n_rep):
            r=[None]*nb_delegue
            vote=[None]*nb_delegue
            index=0
            delegue=0
            #phase de vote des délégués 
            for i in id_delegue:
                
                if delegue <n_direct_d:
                    
                    vote[index]=int(random.randint(0,1))
                    r[index]=cast_vote_with_proof(bb,vote[index],i, j,True)
                    
                    delegue+=1
                else:
                    if delegue==1:
                        vote[index]=0
                    else:
                        vote[index]=choice(range(0,delegue-1))
                    
                    r[index]=copy_vote_with_proof(bb,id_delegue[vote[index]],i,j,True)
                    delegue+=1
                index+=1
        
                    
            #phase de vote des votant
            direct=0
            for i in range(nb_votant_total):
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
        end=timer()
        
        temps[rvi][rdi]=end-start
        
        print(rdi)
        print(rvi)
fig=plt.figure()
ax = plt.axes(projection='3d')
X,Y=np.meshgrid(rendudelegue,votants)
z2 = griddata((rendudelegue, votants), temps, (X,Y))
ax.plot_surface(X, Y, z2,cmap='plasma')
ax.set_xlabel("Nb. de délégués")
ax.set_ylabel("Nb. de votants")
ax.set_zlabel("Temps de calcul (en secondes)")
plt.savefig("graphe3d_300del_3000votants_5curateurs_3réponses.png",dpi=3000)
plt.show()


plt.plot(X[0,:],temps[14,:])
plt.xlabel('Nb. de délégués')
plt.ylabel("Temps de calcul (en secondes)")

plt.savefig("graphe3d_300del_3000votants_5curateurs_3réponses_coupe.png",dpi=3000)
plt.show()
plt.plot(Y[:,0],temps[:,14])
plt.xlabel('Nb. de votants')
plt.ylabel("Temps de calcul (en secondes)")
plt.show()
plt.savefig("graphe3d_300del_3000votants_5curateurs_3réponses_coupe22delegue.png",dpi=3000)





