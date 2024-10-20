#ifndef MAINWINDOW_H
#define MAINWINDOW_H

#include <QMainWindow>

#include "ViewModel/MainViewModel.hpp"

QT_BEGIN_NAMESPACE
namespace Ui {
class MainWindow;
}
QT_END_NAMESPACE

class MainWindow : public QMainWindow
{
    Q_OBJECT

public:
    MainWindow(MainViewModel& viewModel, QWidget *parent = nullptr);
    // This does _not_ destruct the view model; that is the task of the main function.
    ~MainWindow();

public slots:
    void addButtonClicked();
    void asyncButtonClicked();
    // Called by the asyncEnded() signal.
    // The signal-slot mechanism ensures
    // that this always runs on the main thread.
    void onAsyncEnded();

signals:
    // Emitted by the calculation thread
    // when it finishes.
    void asyncEnded();

private:
    Ui::MainWindow *ui;

    // The view model behind the window.
    // This refers to the same object throughout the entire existence of the window;
    // mode changes are achieved by changing the HsCalcStateWrapper instance under the view model.
    MainViewModel& viewModel;

    // Called when trying to add an odd number.
    // Gives the spin box a red color and a tooltip.
    void setError();
    // Returns the spin box to its normal state.
    void unsetError();
};
#endif // MAINWINDOW_H
