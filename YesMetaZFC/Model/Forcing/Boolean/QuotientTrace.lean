import YesMetaZFC.Model.Forcing.Boolean.QuotientProjection
import YesMetaZFC.Model.Forcing.Boolean.PrincipalGraph

/-! # 旧稠密条件在中间商中的迹

在旧正则开条件 X 内，稠密集 E 的主正则开像以上确界 X 为并。
左伴随保持此并，首阶段泛型遂命中其中一个投影。所得旧条件仍属于实际商。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

/-- 对每个实际旧稠密集，商中仍有被首阶段接受的旧条件加强。 -/
def Qtrace_d (j : M.Domain → N.Domain) (B R z Γ : M.Domain) (D : N.Domain) : Prop :=
  ∀ E X, N.mem (j X) D → (∀ p, M.mem p X → ∃ q, Below_d M B R z q p ∧ M.mem q E) →
    ∃ p Y, M.mem p E ∧ M.mem p X ∧ Entry_d M p Y Γ ∧ N.mem (j Y) D

theorem ropen_dense_sup_l {B R z C L V Γ E X : M.Domain}
    (family : ∀ Y, M.mem Y L ↔ Ropen_d B R z Y ∧ M.MemberSubset Y C)
    (order : ∀ Y Z, M.mem Y L → M.mem Z L → (Entry_d M Y Z V ↔ M.MemberSubset Y Z))
    (fn : M.IsSetFunctionFromTo I Γ C L)
    (graph : ∀ p Y, Entry_d M p Y Γ → Rpr_d B R z p Y) (hX : M.mem X L)
    (dense : ∀ p, M.mem p X → ∃ q, Below_d M B R z q p ∧ M.mem q E) :
    ∃ D, (∀ Y, M.mem Y D ↔ ∃ p, M.mem p E ∧ M.mem p X ∧ Entry_d M p Y Γ) ∧
      M.MemberSubset D L ∧ BooleanZF.Bsup_d I L V D X := by
  let ρ : Env M 3 := ⟨fun i => [E,X,Γ].get i,fun _ => E⟩
  let φ : UnarySchema 3 := { body := .existsE (.conj (.mem .newest (.bound 2))
    (.conj (.mem .newest (.bound 3)) (entry_m .newest (.bound 1) (.bound 4)))) }
  obtain ⟨D,members⟩ := ZF.separation_exists_d hZF φ ρ L
  have image Y : M.mem Y D ↔ ∃ p, M.mem p E ∧ M.mem p X ∧ Entry_d M p Y Γ := by
    apply (members Y).trans
    have sat : φ.denote ρ Y ↔ ∃ p, M.mem p E ∧ M.mem p X ∧ Entry_d M p Y Γ := by
      simp only [UnarySchema.denote,φ,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
        Formula.satisfies_mem_iff,entry_sat_l M hZF.1]
      rfl
    apply (and_congr_right fun _ => sat).trans
    exact ⟨And.right,fun ⟨p,pe,px,pY⟩ => ⟨fn.output_mem_of_pairMember pY,p,pe,px,pY⟩⟩
  have sub : M.MemberSubset D L := fun Y hY => by
    obtain ⟨_,_,_,pY⟩ := (image Y).mp hY
    exact fn.output_mem_of_pairMember pY
  refine ⟨D,image,sub,hX,?_,?_⟩
  · intro Y hY
    obtain ⟨p,_,px,pY⟩ := (image Y).mp hY
    exact (order Y X (fn.output_mem_of_pairMember pY) hX).mpr ((graph p Y pY).2.2 X ((family X).mp hX).1 px)
  · intro Y hY upper
    apply (order X Y hX hY).mpr
    intro p px
    have pos := ((family X).mp hX).1.1 p px
    apply ((family Y).mp hY).1.2.2 p pos.1 pos.2
    intro q hq
    have qx := ((family X).mp hX).1.2.1 p q pos.1 hq px
    obtain ⟨r,hr,re⟩ := dense q qx
    have rx := ((family X).mp hX).1.2.1 q r hq.1 hr qx
    obtain ⟨Z,hZ,rZ⟩ := fn.2.2 r (((family X).mp hX).2 r rx)
    exact ⟨r,hr,(order Z Y hZ hY).mp (upper Z ((image Z).mpr ⟨r,re,rx,rZ⟩)) r (graph r Z rZ).2.1⟩

theorem quotient_trace_l {B R z C L V d Γ Q T w K S e u A J P E X a : M.Domain}
    (family : ∀ Y, M.mem Y L ↔ Ropen_d B R z Y ∧ M.MemberSubset Y C)
    (order : ∀ Y Z, M.mem Y L → M.mem Z L → (Entry_d M Y Z V ↔ M.MemberSubset Y Z))
    (target : BooleanZF.Order_d I L V) (empty : ∀ p, ¬ M.mem p d)
    (fn : M.IsSetFunctionFromTo I Γ C L) (graph : ∀ p Y, Entry_d M p Y Γ → Rpr_d B R z p Y)
    (smallOrder : Cond_order_d M Q T w)
    (smallFamily : ∀ U, M.mem U K ↔ Ropen_d Q T w U)
    (smallRelation : ∀ U V, Entry_d M U V S ↔ M.mem U K ∧ M.mem V K ∧ M.MemberSubset U V)
    (source : BooleanZF.Boolean_d I K S e) (interval : BooleanZF.Bi_d I K S u A)
    (hom : M.IsSetFunctionFromTo I J A L) (projection : M.IsSetFunctionFromTo I P L A)
    (adj : ∀ x y, Entry_d M x y P → BooleanZF.Badj_d I A S L V J x y)
    {H : M.Domain → Prop} (generic : Generic_d M Q T w H)
    (xa : Entry_d M X a P) (hit : ∃ q, H q ∧ M.mem q a)
    (dense : ∀ p, M.mem p X → ∃ q, Below_d M B R z q p ∧ M.mem q E) :
    ∃ p Y b, M.mem p E ∧ M.mem p X ∧ Entry_d M p Y Γ ∧ Y ≠ d ∧ Entry_d M Y b P ∧
      (∃ q, H q ∧ M.mem q b) ∧ Entry_d M Y X V := by
  obtain ⟨D,image,sub,sup⟩ := ropen_dense_sup_l hZF family order fn graph (projection.input_mem_of_pairMember xa) dense
  let ρ : Env M 2 := ⟨Fin.cases D (fun _ => P),fun _ => D⟩
  let φ : UnarySchema 2 := { body := .existsE (.conj (.mem .newest (.bound 2)) (entry_m .newest (.bound 1) (.bound 3))) }
  obtain ⟨F,members⟩ := ZF.separation_exists_d hZF φ ρ A
  have imageP b : M.mem b F ↔ ∃ Y, M.mem Y D ∧ Entry_d M Y b P := by
    apply (members b).trans
    have sat : φ.denote ρ b ↔ ∃ Y, M.mem Y D ∧ Entry_d M Y b P := by
      simp only [UnarySchema.denote,φ,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
        Formula.satisfies_mem_iff,entry_sat_l M hZF.1]
      rfl
    apply (and_congr_right fun _ => sat).trans
    exact ⟨And.right,fun ⟨Y,hY,Yb⟩ => ⟨projection.output_mem_of_pairMember Yb,Y,hY,Yb⟩⟩
  have subA : M.MemberSubset F A := fun b hb => by
    obtain ⟨_,_,Yb⟩ := (imageP b).mp hb
    exact projection.output_mem_of_pairMember Yb
  have supA := BooleanZF.Badj_d.sup_l I (interval.boolean_l I source).order target hom projection adj imageP sub sup xa
  have supK := (interval.sup_l I source subA).mp supA
  obtain ⟨b,hb,q,hq,qb⟩ := (ropen_hit_sup_l hZF smallOrder smallFamily smallRelation generic source.order
    (fun b hb => ((interval.carrier b).mp (subA b hb)).1) supK).mp hit
  obtain ⟨Y,hY,Yb⟩ := (imageP b).mp hb
  obtain ⟨p,pe,px,pY⟩ := (image Y).mp hY
  exact ⟨p,Y,b,pe,px,pY,(fun eq => empty p (eq ▸ (graph p Y pY).2.1)),Yb,⟨q,hq,qb⟩,sup.2.1 Y hY⟩

end YesMetaZFC.Model.Forcing.Internal
