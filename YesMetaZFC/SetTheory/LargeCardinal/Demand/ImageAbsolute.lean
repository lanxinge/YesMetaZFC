import YesMetaZFC.SetTheory.LargeCardinal.Types.ContinueAbsolute
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RoundScope
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RawPool
import YesMetaZFC.SetTheory.LargeCardinal.Types.PoolRead

/-! # demanding 回答的同次证书从反射秩层向上还原

只重建原 Vδ 的有限列源；扩展器、超幂、临界像及完整回答沿用原见证。
源前缀 q、完整源元数 n、回答元数 m 在还原前后分别保持。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem td_image_absolute_l {ω η C : M.Domain}
    (hω : M.IsOmega ω) (rankC : V_d I η C) (fs : Fs_read_d ω C)
    (nc : Nonempty {x // M.mem x C}) {s} (ρ : Env (rt_model_l C nc) s)
    (o κ δ q n m U E u τ D w b z pp pb ph : Term s) (σ : Fin 7 → Term s)
    (hw : (o.eval ρ).val = ω) (regular : M.IsRegularCardinal I (δ.eval ρ).val)
    (valid : Formula.satisfies ρ (td_image_m o κ δ q n m U E u τ D w b z pp pb ph σ)) :
    ∃ L W, M.mem L C ∧ M.mem W C ∧ ∃ X K R F c d Y T j κ' U' E' u',
      Td_image_at_d (ZF.modelsKP hZF) ω (κ.eval ρ).val (δ.eval ρ).val
        (q.eval ρ).val (n.eval ρ).val (m.eval ρ).val (U.eval ρ).val (E.eval ρ).val
        (u.eval ρ).val (τ.eval ρ).val (D.eval ρ).val (w.eval ρ).val (b.eval ρ).val
        (z.eval ρ).val (pp.eval ρ).val (pb.eval ρ).val (ph.eval ρ).val
        (fun i => ((σ i).eval ρ).val) L W X K R F c d Y T j κ' U' E' u' := by
  simp only [td_image_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff] at valid
  obtain ⟨X,K',R₀,L,F,c,d,Y,T,j,κ',U',E',u',core,queryRank,pool,reply⟩ := valid
  let ε := ρ.push X |>.push K' |>.push R₀ |>.push L |>.push F |>.push c |>.push d |>.push Y
    |>.push T |>.push j |>.push κ' |>.push U' |>.push E' |>.push u'
  let a (t : Term s) := t.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
  let t (i : Fin 14) : Term (s+14) := .bound ⟨i.val,by omega⟩
  obtain ⟨rank,K₀,source,hLδ,hκL,hτL,loc,card,strong,mx,my,ultra,crit,bound,limit,hU,hE,hu⟩ :=
    ti_image_absolute_l hZFC hω rankC fs nc ε (a o) (a κ) (a δ) (a τ) (a U) (a E) (a u)
      (t 13) (t 12) (t 11) (t 10) (t 9) (t 8) (t 7) (t 6) (t 5) (t 4) (t 3) (t 2) (t 1) (t 0)
      (by simpa only [ε,a,Definitional.Term.eval_weaken] using hw)
      (by simpa only [ε,a,Definitional.Term.eval_weaken] using regular) core
  simp only [ε,a,Definitional.Term.eval_weaken] at rank source hLδ hκL hτL loc card strong mx my ultra crit bound limit hU hE hu
  obtain ⟨W,rankW,hDW⟩ := queryRank
  have rankW := (vr_sat_l (ZF.modelsKP hZF) fs.transitive nc _ _ _).mp rankW
  simp only [Definitional.Term.eval_weaken,Definitional.Term.eval_newest] at rankW hDW
  have lo := (loc.ordinals_l (ZF.modelsKP hZF) source.transitive source.code).2
  obtain ⟨V,rv⟩ := ZF.v_exists_l I hZF lo
  have hVC := ZF.v_mem_l I hZF rv rankC (ZF.v_ordinal_height_l hZF rankC lo L.property)
  have eq := vr_agree_l hZF fs.transitive W.property rv (fs.transitive V hVC) rankW
  have fullW : V_d I L.val W.val := by rw [eq]; exact rv
  obtain ⟨A,H,_,_,names,seq,product⟩ :=
    (fs.pool_sat_l (ZF.modelsKP hZF) nc ε (a o) (a q) (t 2) (t 1)
      (by simpa only [ε,a,Definitional.Term.eval_weaken] using hw)).mp pool
  simp only [ε,a,Definitional.Term.eval_weaken] at names seq product
  have reply := td_reply_source_l (ZF.modelsKP hZF) fs.transitive nc fs.pair
    (valid := reply)
  simp only [Definitional.Term.eval_weaken,Definitional.Term.eval_newest,hw] at reply
  have slots (f : Fin 7 → Term (s+14)) :
      Fin.cases (f 0) (Fin.cases (f 1) (Fin.cases (f 2) (Fin.cases (f 3)
        (Fin.cases (f 4) (Fin.cases (f 5) (fun _ => f 6)))))) = f := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))) i
  simp only [slots (fun i => a (σ i)),a,Definitional.Term.eval_weaken] at reply
  exact ⟨L.val,W.val,L.property,W.property,
    X.val,K₀,R₀.val,F.val,c.val,d.val,Y.val,T.val,j.val,κ'.val,U'.val,E'.val,u'.val,
    rank,source,hLδ,hκL,hτL,fullW,hDW,loc,card,strong,mx,my,ultra,crit,bound,limit,
    hU,hE,hu,⟨A,H,names,seq,product⟩,reply⟩

/-- 完整轮自身提供 δ 的正则性及新域的极限性，不把它们交给调用方猜测。 -/
theorem td_round_image_l {ω η C : M.Domain}
    (hω : M.IsOmega ω) (rankC : V_d I η C) (limitC : M.IsLimitOrdinal η)
    (fs : Fs_read_d ω C) (nc : Nonempty {x // M.mem x C})
    (ρ : Env (rt_model_l C nc) 62) (valid : Formula.satisfies ρ td_round0_m)
    (hw : (ρ.bound 19).val = ω) :
    M.IsLimitOrdinal (ρ.bound 21).val ∧ M.IsLimitOrdinal (ρ.bound 0).val ∧
    M.mem (ρ.bound 24).val (ρ.bound 0).val ∧ M.mem (ρ.bound 43).val (ρ.bound 0).val ∧
    ∃ L W, M.mem L C ∧ M.mem W C ∧ ∃ X K R F c d Y T j κ' U' E' u',
      Td_image_at_d (ZF.modelsKP hZF) ω (ρ.bound 24).val (ρ.bound 21).val
        (ρ.bound 27).val (ρ.bound 28).val (ρ.bound 9).val (ρ.bound 35).val (ρ.bound 36).val
        (ρ.bound 38).val (ρ.bound 0).val (ρ.bound 3).val (ρ.bound 4).val (ρ.bound 40).val
        (ρ.bound 42).val (ρ.bound 16).val (ρ.bound 17).val (ρ.bound 18).val
        (fun i => (ρ.bound ⟨55+i.val,by omega⟩).val) L W X K R F c d Y T j κ' U' E' u' := by
  obtain ⟨seed,data⟩ := (Formula.satisfies_conj_iff ..).mp valid
  have seed := (Formula.satisfies_rename ..).mp seed
  simp only [td_seed0_m,td_seed_m,Formula.satisfies_conj_iff] at seed
  have regular := ti_woodin_regular_l (ZF.modelsKP hZF) rankC limitC fs nc _ (.bound 2) seed.2.2.1
  simp only [td_witness0_m,td_round_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at data
  obtain ⟨above,growth,_,_,_,_,language,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,image⟩ := data
  have language := language
  simp only [ee_language_m,Formula.satisfies_bind,ee_language0_m,Formula.satisfies_conj_iff] at language
  have limit := (rt_limit_l fs.transitive nc (ZF.modelsKP hZF) (ρ.bound 0)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp language.2.1)
  refine ⟨regular.isLimitOrdinal,limit,growth,above,?_⟩
  let s : Fin 7 → Term 62 := fun i => .bound ⟨55+i.val,by omega⟩
  exact td_image_absolute_l hZFC hω rankC fs nc ρ
    (.bound 19) (.bound 24) (.bound 21) (.bound 27) (.bound 28) (.bound 9)
    (.bound 35) (.bound 36) (.bound 38) (.bound 0) (.bound 3) (.bound 4)
    (.bound 40) (.bound 42) (.bound 16) (.bound 17) (.bound 18) s hw regular image

end YesMetaZFC.SetTheory.LargeCardinal
