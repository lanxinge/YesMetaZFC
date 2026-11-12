import YesMetaZFC.Model.Forcing.Boolean.QuotientLift

/-! # 实际商滤子对中间模型的泛型性

对中间模型任意稠密集取其首阶段名称，以真值定理取得密度证书；
提升定理在原代数中产生稠密集，原泛型的命中再通过首阶段真值定理读回。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}

def Qgeneric_d (j : M.Domain → N.Domain) (G : M.Domain → Prop) (x : N.Domain) : Prop :=
  ∃ b, G b ∧ j b = x

variable (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem quotient_generic_l {Q T w K S e u A L V d J P c τ : M.Domain}
    (O : Cond_order_d M Q T w)
    (family : ∀ a, M.mem a K ↔ Ropen_d Q T w a)
    (order : ∀ a b, Entry_d M a b S ↔ M.mem a K ∧ M.mem b K ∧ M.MemberSubset a b)
    (source : BooleanZF.Boolean_d I K S e) (empty : ∀ q, ¬ M.mem q e)
    (interval : BooleanZF.Bi_d I K S u A) (target : BooleanZF.Boolean_d I L V d)
    (hom : BooleanZF.Bh_d I A S e L V d J) (fn : M.IsSetFunctionFromTo I P L A)
    (adj : ∀ b a, Entry_d M b a P → BooleanZF.Badj_d I A S L V J b a)
    {H G : M.Domain → Prop} (small : Generic_d M Q T w H) (big : Generic_d M L V d G)
    (read : ∀ a y, Entry_d M a y J → (G y ↔ ∃ q, H q ∧ M.mem q a))
    (hitU : ∃ q, H q ∧ M.mem q u) (hc : H c) (name : Qname_d Q c L d P τ)
    (j : M.Domain → (extension_l M hZF Q T w H).Domain) (inj : Function.Injective j)
    (full : ∀ a y, (extension_l M hZF Q T w H).mem y (j a) ↔ ∃ b, M.mem b a ∧ j b = y)
    (checks : ∀ a t, Check_d M c a t → Qval_d M Q T w H t (j a))
    {D : (extension_l M hZF Q T w H).Domain} (quotient : Qread_d j H A L V d J D)
    (value : Qval_d M Q T w H τ D) :
    Generic_d (extension_l M hZF Q T w H) D (j V) (j d) (Qgeneric_d j G) := by
  let E := extension_l M hZF Q T w H
  have hE := preserves_zf_l O hZF small
  have hcQ := (small.proper c hc).1
  have entry := image_entry_iff_l j inj full (KP.exists_pair (ZF.modelsKP hZF)) hE.1
  have accepted {x} (hx : G x) : E.mem (j x) D := by
    refine (quotient (j x)).mpr ⟨x,(big.proper x hx).1,(big.proper x hx).2,rfl,fun a y _ hit ay => ?_⟩
    obtain ⟨z,hz,zx,zy⟩ := big.directed x y hx ((read a y ay).mpr hit)
    exact ⟨z,⟨(big.proper z hz).1,(big.proper z hz).2,zx⟩,zy⟩
  have positive {x} (hx : E.mem x D) : x ≠ j d := by
    obtain ⟨b,_,nz,rfl,_⟩ := (quotient x).mp hx
    exact fun eq => nz (inj eq)
  refine ⟨?_,?_,?_,?_,?_⟩
  · rintro x ⟨b,hb,rfl⟩
    exact ⟨accepted hb,positive (accepted hb)⟩
  · obtain ⟨x,hx⟩ := big.inhabited
    exact ⟨j x,x,hx,rfl⟩
  · rintro x y ⟨b,hb,rfl⟩ hy xy
    obtain ⟨a,ha,_,rfl,_⟩ := (quotient y).mp hy
    exact ⟨a,big.upward b a hb ha ((entry b a V).mpr xy),rfl⟩
  · rintro x y ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩
    obtain ⟨s,hs,sa,sb⟩ := big.directed a b ha hb
    exact ⟨j s,⟨s,hs,rfl⟩,(entry s a V).mp sa,(entry s b V).mp sb⟩
  · rintro y ⟨x,hx,rfl⟩ F dense
    obtain ⟨σ,nσ,vσ⟩ := value_name_l F
    obtain ⟨ν,relation,nν,_⟩ := zf_check_l M hZF hcQ V
    obtain ⟨t,check,nt,_⟩ := zf_check_l M hZF hcQ x
    let ρ := stage_env_l M τ ν σ t
    let η := stage_env_l E D (j V) F (j x)
    let φ : Formula 1 4 := stage_dense_m (.bound 3) (.bound 2) (.bound 1) (.bound 0)
    have closed : φ.FreeClosed := stage_dense_m_freeClosed _ _ _ _ rfl rfl rfl rfl
    have values : Env_val_d hZF ρ η := by
      intro a
      cases a with
      | free _ => exact value
      | bound i => exact Fin.cases (checks x t check) (Fin.cases vσ (Fin.cases (checks V ν relation) (fun _ => value))) i
    have hd : Stage_dense_d E D (j V) F (j x) := by
      intro y hy yx
      obtain ⟨z,hz,zF⟩ := dense y ⟨hy,positive hy,yx⟩
      exact ⟨z,hz.1,hz.2.2,zF⟩
    obtain ⟨p,hp,force⟩ := (forcing_truth_l O hZF small φ closed ρ η values).mpr
      ((stage_dense_sat_l E hE.1 η _ _ _ _).mpr hd)
    -- 同时保持密度证书、检查名字的基条件以及忠实区间的顶。
    obtain ⟨r,hr,ru⟩ := hitU
    obtain ⟨s,hs,sp,sc⟩ := small.directed p c hp hc
    obtain ⟨q,hq,qs,qr⟩ := small.directed s r hs hr
    have hq' := small.proper q hq
    have qc : Below_d M Q T w q c := ⟨hq'.1,hq'.2,
      O.trans q s c hq'.1 (small.proper s hs).1 hcQ qs sc⟩
    have qp : Below_d M Q T w q p := ⟨hq'.1,hq'.2,
      O.trans q s p hq'.1 (small.proper s hs).1 (small.proper p hp).1 qs sp⟩
    have qu := ((family u).mp interval.bound).2.1 r q (small.proper r hr).1 ⟨hq'.1,hq'.2,qr⟩ ru
    obtain ⟨a,regular,qa,minimal⟩ := ropen_condition_l hZF O hq'.1 hq'.2
    have haK := (family a).mpr regular
    have ha := (interval.carrier a).mpr ⟨haK,(order a u).mpr ⟨haK,interval.bound,
      minimal u ((family u).mp interval.bound) qu⟩⟩
    obtain ⟨b,hb,ab⟩ := hom.function.2.2 a ha
    have gb := (read a b ab).mpr ⟨q,hq,qa⟩
    obtain ⟨X,meet⟩ := target.meet x b (big.proper x hx).1 hb
    obtain ⟨s,gs,sx,sb⟩ := big.directed x b hx gb
    have gX := big.upward s X gs meet.1 ((meet.2 s (big.proper s gs).1).mpr ⟨sx,sb⟩)
    have named : ∀ t : Term 4, Name_d M Q (t.eval ρ) := fun t => qval_name_l (values t)
    have lower := (forces_regular_l O hZF φ ρ named).1 p q (small.proper p hp).1 qp force
    have bounds := BooleanZF.meet_bounds_d I target.order meet
    have lift := quotient_dense_l hZF O family order source empty interval target hom fn adj hcQ name relation nσ check
      qc ab minimal meet.1 bounds.2 bounds.1 (big.proper x hx).1 lower
    obtain ⟨Z,gZ,q',a',b',x',t',qc',ha',qa',minimal',ab',hx',Zb',Zx',check',force'⟩ :=
      generic_pick_l hZF big (qhit_defined_l hZF Q T w c A J L V σ) gX lift
    have gb' := big.upward Z b' gZ (hom.function.output_mem_of_pairMember ab') Zb'
    have hq' := (ropen_condition_hit_l hZF O qc'.1 qc'.2.1 qa' minimal' small).mp ((read a' b' ab').mp gb')
    have gx' := big.upward Z x' gZ hx' Zx'
    exact ⟨j x',⟨x',gx',rfl⟩,(qval_mem_forcing_l O hZF small (checks x' t' check') vσ).mp ⟨q',hq',force'⟩⟩

end YesMetaZFC.Model.Forcing.Internal
