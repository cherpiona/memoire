# -*- coding: utf-8 -*-
"""
Created on Sun Aug  7 01:07:37 2022

@author: moi
"""
import json
import hashlib
import canonicaljson
import elgamal
from random import randint
from vote_dproof import verify_ballot, generate_ballot

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


"""
    ELECTION INITIALIZATION

"""

def inverse(x, p):
    """
    @returns x^-1 in Z*_p
    """

    res = pow(x, p-2, p)
    assert (res * x) % p == 1
    return res
def combine_keys(G, partial_keys):
    """
    Given the partial keys of the trustees, combine them to obtain the key of the election.
    """
    #assert [key[1].G == G for key in partial_keys]    
    #assert [key[1] == key[0].pk() for key in partial_keys]

    pk=partial_keys[0].y

    index=0
    for key in partial_keys:
        if index!=0:

            pk=pk*key.y %G.p
            
        index+=1
    return elgamal.ElgamalPublicKey(G, pk)

def prove_key_correctness(elgamal_key):
    """
    Given an elgamal key, return a valid proof of knowledge of the secret key.
    To do so, use the _hashg method.
    """
    pk = elgamal_key.pk().y
    group=elgamal_key.G
    sk,commit = elgamal.gen_elgamal_keypair(group)
    challenge=_hashg(json.dumps({
                "commit": commit.y,
                "pk": pk,
                }), group.q)
    response = sk.x+challenge*elgamal_key.x %group.q 

    return {"pk": pk,
            "commit": commit,
            "response": response}

def validate_key_correctness(key,group):
    """
    Given a proof of knowledge of the secret key of an elgamal key,
    verify that the proof is correct.
    """

    pk = key["pk"] 
    commit = key["commit"] 
    response = key["response"]
    group=elgamal.ElGamalGroup(group["p"],group["g"])
    challenge=_hashg(json.dumps({
                "commit": commit,
                "pk": pk,
                }), group.q)
    if pow(group.g,response,group.p)==commit*pow(pk,challenge,group.p)%group.p:
        return True
    # Verify the proof

    return False

def generate_empty_bb(p, g, pk):
    return {"group": {"p": p, "g": g}, "pk": pk, "ballots": []}

def generate_election(n_trustees, p = None, g = None):
    if p == None or g == None:
        G = elgamal.gen_group()
        p = G.p
        g = G.g
    else:
        G = elgamal.ElGamalGroup(p, g)
    partial_keys = [elgamal.gen_elgamal_keypair(G) for i in range(n_trustees)]
    public_keys=[]
    secret_keys=[]
    for key in partial_keys:
        public_keys.append(key[1])
        secret_keys.append(key[0])
    pk = combine_keys(G, public_keys)
    
    bb = generate_empty_bb(p, g, pk.y)
    
    bb["tallier_keys"] = [prove_key_correctness(key) for key in secret_keys]
    return bb, secret_keys

"""
    VOTING PHASE
"""

def cast_vote(bb, vote):
    """
    Given the bulletin board bb of an election and a 0-1 vote, update 
    the bulletin board with a valid ballot of the vote.
    """
    #assert vote in (0, 1)
    group=elgamal.ElgamalGroup(bb["group"]["p"],bb["group"]["g"])
    public_key=elgamal.ElgamalPublicKey(group,bb["pk"])
    ballot = generate_ballot(public_key, vote)
    bb["ballots"].append(ballot)
def copie_vote(bb,id_copie):
    "update le bb avec la copie d'un vote, la preuve est distinguable"
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
    
"""
    COMPUTATION OF THE DECRYPTION FACTORS  
"""

def compute_tally_encryption(bb):
    """ 
    Given the bulletin board bb of an election, return a valid encryption
    of the result of the election.
    """
    group=elgamal.ElgamalGroup(bb["group"]["p"],bb["group"]["g"])
    
    #pk=combine_keys(group,bb["tallier_keys"])
    public_key=elgamal.ElgamalPublicKey(group,bb["pk"])
    encrypted_tally=elgamal.ElgamalCiphertext(group,bb["ballots"][0]["ct"]["c1"],bb["ballots"][0]["ct"]["c2"])
    index=1
    for ballots in bb["ballots"]:
        ###verifier preuve avant
        
        ballot=elgamal.ElgamalCiphertext(group,ballots["ct"]["c1"],ballots["ct"]["c2"])

        assert verify_ballot(public_key,ballots),"erreur sur le preuve du ballot numero {}".format(index)
        
        if index!=1:

            encrypted_tally=encrypted_tally.homomorphic_add(ballot)

        index+=1
    return encrypted_tally

def compute_decryption_factor_without_proof(tally_encryption, partial_key):
    """
    Given an encryption of the tally and the partial key of a trustee,
    compute the corresponding decryption factor.
    """

    df = pow(tally_encryption.c1,partial_key.x,partial_key.G.p) % partial_key.G.p
    

    return df


def compute_decryption_factor_with_proof(tally_encryption, partial_key):
    """
    Given an encryption of the tally and the partial key of a trustee,
    compute the corresponding decryption factor and the corresponding proof of 
    correct computation.
    To do so, use the _hashg method.
    """

    pk = partial_key.pk()
    
    c1 = tally_encryption.c1
    
    group=tally_encryption.G
    df = compute_decryption_factor_without_proof(tally_encryption,partial_key) 
    s=randint(0, group.q-1)
    commit = [pow(group.g,s,group.p),pow(c1,s,group.p)]

    challenge=_hashg(json.dumps({
                    " pk ": pk.y,
                    " c1 ": c1,
                    " decryption_factor ": df ,
                    " commit ": commit 
                    }), group.q)
    response = s+challenge*partial_key.x % group.q
    
    return {"pk": pk.y,
            "c1": c1,
            "decryption_factor": df,
            "commit": commit,
            "response": response
            }

def validate_decryption_factor_proof(decryption_factor,group):
    """
    Given a proof of correctness of a decryption factor,
    verify that the proof is correct.
    """

    pk = decryption_factor["pk"]
    c1 = decryption_factor["c1"]
    df = decryption_factor["decryption_factor"]
    commit = decryption_factor["commit"]
    response = decryption_factor["response"]
    
    challenge=_hashg(json.dumps({
                " pk ": pk,
                " c1 ": c1,
                " decryption_factor ": df ,
                " commit ": commit 
                }), group.q)
    # Verify the proof

    if pow(group.g,response,group.p)== commit[0]*pow(pk,challenge,group.p)%group.p:
        if pow(c1,response,group.p)== commit[1]*pow(df,challenge,group.p)%group.p:
            return True
    

    
    return False


def compute_all_decryption_factors(bb, partial_keys):
    tally_encryption = compute_tally_encryption(bb)
    decryption_factors = [compute_decryption_factor_with_proof(tally_encryption, key)
                            for key in partial_keys]
    
    bb["decryption_factors"] = decryption_factors 

"""
    COMPUTE THE FINAL RESULT OF THE ELECTION
"""

def combine_decryption_factors(bb):
    """
    Given the bulletin board bb of an election with the decryption factors,
    comptue the final result.
    """

    encrypted_tally=compute_tally_encryption(bb)
    group=elgamal.ElgamalGroup(bb["group"]["p"],bb["group"]["g"])




        
    #fusion partiel decryption 
    df=bb["decryption_factors"][0]["decryption_factor"]
    
    index=1
    for dfpartiel in bb["decryption_factors"]:
        
        assert validate_decryption_factor_proof(dfpartiel,group),"erreur dans la preuve de part de déchiffrement {}".format(index)
        if index!=1:     
            df=df*dfpartiel["decryption_factor"] % group.p
        index+=1
        
    res = encrypted_tally.c2*inverse(df,group.p)%group.p
    
    return res

def tally(bb):
    """
    Given the bulletin board bb of an election with the decryption factors,
    validate the correctness of the bulletin board and compute the final result.
    Return None if one of the trustees has cheated.
    """
    # QUESTION 5.2
    
    # Verify the proofs and compute the result
    
    
    g_m=combine_decryption_factors(bb)
    group=elgamal.ElgamalGroup(bb["group"]["p"],bb["group"]["g"])
    m = elgamal.dLog(group.p, group.g, g_m)
    index=1
    for df in bb["decryption_factors"]:
        assert validate_decryption_factor_proof(df,group),"erreur sur la preuve de part de chiffrement {}".format(index)
        if validate_decryption_factor_proof(df,group)==False:
        
            return None
        index+=1
    return m









#with open("bb_proof.json", "r") as fd:
 #   bb = json.loads(fd.readline())

#    m=tally(bb)
#genere une election avec 3 curateurs
bb,partial_keys=generate_election(10)
#phase de vote
cast_vote(bb,1)
cast_vote(bb,1)
cast_vote(bb,1)

cast_vote(bb,0)
cast_vote(bb,0)
cast_vote(bb,1)
cast_vote(bb,1)
copie_vote(bb, 1)
copie_vote(bb,4)

#cast_vote(bb,2) erreur au déchiffrement
#phase de déchiffrement
#les curateurs calculent leur part de déchiffrement
compute_all_decryption_factors(bb,partial_keys)

res=tally(bb)
print(res)












