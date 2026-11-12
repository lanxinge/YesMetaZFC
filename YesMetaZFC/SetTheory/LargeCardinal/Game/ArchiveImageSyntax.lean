import YesMetaZFC.SetTheory.LargeCardinal.Game.ArchiveImage
import YesMetaZFC.SetTheory.LargeCardinal.Game.ArchiveSyntax

/-! # 同一原档案五坐标像的完整一阶公式

一次量化十三项原行、五十四项原存档、行码及锥腿。公式保留原档案索引、
节点、完整存档与五个实际像，供背景替换收集指定分支中的真实节点列。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_archive_image_m {d} (D P m i : Term d) (v : Fin 5 → Term d) : Formula 1 d :=
  let e : Term d → Term (69+d) := fun t => t.rename (Fin.natAdd 69)
  let s : Fin 13 → Term (69+d) := fun k => .bound ((k.castAdd 56).castAdd d)
  let w : Fin 54 → Term (69+d) := fun k => .bound ((Fin.natAdd 13 (k.castAdd 2)).castAdd d)
  let r : Term (69+d) := .bound ((67 : Fin 69).castAdd d)
  let j : Term (69+d) := .bound ((68 : Fin 69).castAdd d)
  rb_exists_m (n := 69) (.conj (rd_entry0_m (e m) r (e D))
    (.conj (rt_tuple_m s r) (.conj (Formula.extensionalEq (s 0) (e i))
      (.conj (tg_saved_code_m (s 2) (s 3) (s 4) (s 8) (s 9) w)
        (.conj (rd_entry0_m (e i) j (e P))
          (rb_conj_m (fun a : Fin 5 => rd_entry0_m (w ([22,19,40,41,42].get a)) (e (v a)) j)))))))

@[simp] theorem tg_archive_image_closed_l {d} (D P m i : Term d) (v : Fin 5 → Term d)
    (hD : D.freeSupport = []) (hP : P.freeSupport = []) (hm : m.freeSupport = [])
    (hi : i.freeSupport = []) (hv : ∀ a, (v a).freeSupport = []) : (tg_archive_image_m D P m i v).FreeClosed := by
  simp -implicitDefEqProofs [tg_archive_image_m,Definitional.Formula.FreeClosed,hD,hP,hm,hi,hv]
  exact rt_tuple_closed_l _ _ (fun _ => rfl) rfl

theorem tg_archive_image_sat_l (hE : Extensional M) {d} (ρ : Env M d)
    (D P m i : Term d) (v : Fin 5 → Term d) :
    Formula.satisfies ρ (tg_archive_image_m D P m i v) ↔
      Tg_archive_image_d (D.eval ρ) (P.eval ρ) (m.eval ρ) (i.eval ρ) (fun a => (v a).eval ρ) := by
  simp only [tg_archive_image_m,rb_exists_sat_l,Formula.satisfies_conj_iff,rd_entry0_sat_l hE,
    rt_tuple_sat_l hE,Formula.satisfies_extensionalEq_iff_eq hE,tg_saved_code_sat_l,rb_conj_sat_l,
    rb_old_eval_l,Term.eval_bound,Fin.addCases_left]
  constructor
  · rintro ⟨u,entry,pack,index,code,leg,images⟩
    refine ⟨u 67,Tg_archive_row_d.from_values_d (fun k => u (k.castAdd 56)),entry,?_,index,
      (fun k => u (Fin.natAdd 13 (k.castAdd 2))),code,u 68,leg,images⟩
    simpa only [Tg_archive_row_d.values_from_l] using pack
  · rintro ⟨r,row,entry,pack,index,w,code,j,leg,images⟩
    let tail : Fin 56 → M.Domain := Fin.addCases (m := 54) (n := 2) (motive := fun _ => M.Domain)
      w (fun k : Fin 2 => [r,j].get k)
    let u : Fin 69 → M.Domain := Fin.addCases (m := 13) (n := 56) (motive := fun _ => M.Domain) row.values_d tail
    have rs : (fun k : Fin 13 => u (k.castAdd 56)) = row.values_d :=
      funext (fun k => Fin.addCases_left (m := 13) (n := 56) (motive := fun _ => M.Domain)
        (left := row.values_d) (right := tail) k)
    have ws : (fun k : Fin 54 => u (Fin.natAdd 13 (k.castAdd 2))) = w := by
      funext k
      simp only [u,tail,Fin.addCases_right,Fin.addCases_left]
    refine ⟨u,entry,?_,index,?_,leg,?_⟩
    · exact Eq.mpr (congrArg (fun v => Rt_tuple_d v r) rs) pack
    · rw [ws]
      exact code
    · exact Eq.mpr (congrArg (fun w => ∀ a : Fin 5,
        Rd_entry_d (w ([22,19,40,41,42].get a)) ((v a).eval ρ) j) ws) images

def Tg_archive_row_image_d (D P i r : M.Domain) : Prop := ∃ m, ∃ v : Fin 5 → M.Domain,
  Tg_archive_image_d D P m i v ∧ Rt_tuple_d v r

def tg_archive_row_image_m {d} (D P i r : Term d) : Formula 1 d := .existsE (
  let e : Term (d+1) → Term (5+(d+1)) := fun t => t.rename (Fin.natAdd 5)
  let v : Fin 5 → Term (5+(d+1)) := fun k => .bound (k.castAdd (d+1))
  rb_exists_m (n := 5) (.conj (tg_archive_image_m (e D.weaken) (e P.weaken) (e .newest) (e i.weaken) v)
    (rt_tuple_m v (e r.weaken))))

@[simp] theorem tg_archive_row_image_closed_l {d} (D P i r : Term d)
    (hD : D.freeSupport = []) (hP : P.freeSupport = []) (hi : i.freeSupport = []) (hr : r.freeSupport = []) :
    (tg_archive_row_image_m D P i r).FreeClosed := by
  simp -implicitDefEqProofs [tg_archive_row_image_m,Definitional.Formula.FreeClosed,hD,hP,hi]
  exact rt_tuple_closed_l _ _ (fun _ => rfl) (by simpa using hr)

theorem tg_archive_row_image_sat_l (hE : Extensional M) {d} (ρ : Env M d) (D P i r : Term d) :
    Formula.satisfies ρ (tg_archive_row_image_m D P i r) ↔
      Tg_archive_row_image_d (D.eval ρ) (P.eval ρ) (i.eval ρ) (r.eval ρ) := by
  simp only [tg_archive_row_image_m,Tg_archive_row_image_d,Formula.satisfies_exists_iff,
    rb_exists_sat_l,Formula.satisfies_conj_iff,tg_archive_image_sat_l hE,rt_tuple_sat_l hE,
    rb_old_eval_l,Definitional.Term.eval_weaken,Definitional.Term.eval_newest,Term.eval_bound,Fin.addCases_left]

end YesMetaZFC.SetTheory.LargeCardinal
